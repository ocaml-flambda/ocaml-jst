open Lambda
open Typedtree
open Asttypes

(** Convenience functions for working with the Lambda AST *)
module Lambda_utils = struct
  (** Creating AST fragments *)
  module Make = struct
    (** Lambda integer literals *)
    let int n = Lconst (const_int n)

    (** Lambda float literals; be careful with unusual values, as this calls
        [Float.to_string] *)
    let float f = Lconst (Const_base (Const_float (Float.to_string f)))

    (** Lambda string literals; these require a location, and are constructed as
        "quoted strings", not {fancy|delimited strings|fancy}. *)
    let string ~loc s = Lconst (Const_base (Const_string(s, loc, None)))
  end

  (** Nicer OCaml syntax for constructing Lambda ASTs that operate on integers;
      created by [int_ops], which includes the necessary location in all the
      operations *)
  module type Int_ops = sig
    (* We want to expose all the operators so we don't have to think about which
       ones to add and remove as we change the rest of the file *)
    [@@@warning "-32"]

    (** Integer arithmetic *)

    val ( + ) : lambda -> lambda -> lambda
    val ( - ) : lambda -> lambda -> lambda
    val ( * ) : lambda -> lambda -> lambda
    val ( / ) : lambda -> lambda -> lambda

    (** Integer comparisons *)

    val ( = )  : lambda -> lambda -> lambda
    val ( <> ) : lambda -> lambda -> lambda
    val ( < )  : lambda -> lambda -> lambda
    val ( > )  : lambda -> lambda -> lambda
    val ( <= ) : lambda -> lambda -> lambda
    val ( >= ) : lambda -> lambda -> lambda

    (** Boolean logical operators *)

    val ( && ) : lambda -> lambda -> lambda
    val ( || ) : lambda -> lambda -> lambda

    (** Integer literals *)
    val l0 : lambda
    val l1 : lambda
    val i  : int -> lambda
  end

  (** Construct an [Int_ops] module at the given location *)
  let int_ops ~loc : (module Int_ops) = (module struct
    let binop prim l r = Lprim(prim, [l; r], loc)

    let ( + )  = binop Paddint
    let ( - )  = binop Psubint
    let ( * )  = binop Pmulint
    let ( / )  = binop (Pdivint Unsafe)
    let ( = )  = binop (Pintcomp Ceq)
    let ( <> ) = binop (Pintcomp Cne)
    let ( < )  = binop (Pintcomp Clt)
    let ( > )  = binop (Pintcomp Cgt)
    let ( <= ) = binop (Pintcomp Cle)
    let ( >= ) = binop (Pintcomp Cge)
    let ( && ) = binop Psequor
    let ( || ) = binop Psequor

    let i n = Lconst (const_int n)
    let l0 = i 0
    let l1 = i 1
  end)
end

(** Sometimes the generated code for array comprehensions reuses certain
    expressions more than once, and sometimes it uses them exactly once. We want
    to avoid using let bindings in the case where the expressions are used
    exactly once, so this module lets us check statically whether the let
    bindings have been created.

    The precise context is that the endpoints of integer ranges and the lengths
    of arrays are used once (as `for` loop endpoints) in the case where the
    array size is not fixed and the array has to be grown dynamically; however,
    they are used multiple times if the array size is fixed, as they are used to
    precompute the size of the newly-allocated array.  Because, in the
    fixed-size case, we need both the bare fact that the bindings exist as well
    as to do computation on these bindings, we can't simply maintain a list of
    bindings; thus, this module, allowing us to work with
    [(Usage.once, Let_binding.t) Usage.if_reused] in the dynamic-size case and
    [(Usage.many, Let_binding.t) Usage.if_reused] in the fixed-size case (as
    as similar [Usage.if_reused] types wrapping other binding-representing
    values). *)
module Usage = struct
  (** A two-state (boolean) type-level enum indicating whether a value is used
      exactly [once] or can be used [many] times *)

  type once = private Once [@@warning "-37"]
  type many = private Many [@@warning "-37"]

  (** The singleton reifying the above type-level enum, indicating whether
      values are to be used exactly [Once] or can be reused [Many] times *)
  type _ t =
    | Once : once t
    | Many : many t

  (** An option-like type for storing extra data that's necessary exactly when a
      value is to be reused [many] times *)
  type (_, 'a) if_reused =
    | Used_once : (once, _) if_reused
    | Reusable  : 'a -> (many, 'a) if_reused
end

(** First-class let bindings; we sometimes need to collect these while
    translating array comprehension clauses and bind them later *)
module Let_binding = struct
  (** The first-class (in OCaml) type of let bindings *)
  type t =
    { let_kind   : let_kind
    ; value_kind : value_kind
    ; id         : Ident.t
    ; init       : lambda }

  (** Create a let binding *)
  let make let_kind value_kind id init =
    {let_kind; value_kind; id; init}

  (** Create a a fresh local identifier to bind (from a string), and return that
      it along with the corresponding let binding *)
  let make_id let_kind value_kind name init =
    let id = Ident.create_local name in
    id, make let_kind value_kind id init

  (** Create a a fresh local identifier to bind (from a string), and return that
      it along with the Lambda variable (with [Lvar]) for it and the
      corresponding let binding *)
  let make_id_var let_kind value_kind name init =
    let id, binding = make_id let_kind value_kind name init in
    id, Lvar id, binding

  (** Create a a fresh local identifier to bind (from a string), and return its
      corresponding Lambda variable (with [Lvar]) and let binding *)
  let make_var let_kind value_kind name init =
    let _id, var, binding = make_id_var let_kind value_kind name init in
    var, binding

  (** Create a Lambda let-binding (with [Llet]) from a first-class let
      binding *)
  let let_one {let_kind; value_kind; id; init} body =
    Llet(let_kind, value_kind, id, init, body)

  (** Create Lambda let-bindings (with [Llet]) from multiple first-class let
      bindings *)
  let let_all = List.fold_right let_one

  (** Creates a new let binding only if necessary: if the value is to be used
      (as per [usage]) [Once], then we don't need to create a binding, so we
      just return it.  However, if the value is to be reused [Many] times, then
      we create a binding with a fresh variable and return the variable (as a
      lambda term).  Thus, in an environment where the returned binding is used,
      the lambda term refers to the same value in either case. *)
  let make_if_reused (type u)
        ~(usage:u Usage.t) let_kind value_kind name value
      : lambda * (u, t) Usage.if_reused =
    match usage with
    | Once ->
        value, Used_once
    | Many ->
        let var, binding = make_var let_kind value_kind name value in
        var, Reusable binding
end

module Precompute_array_size = struct
  open Lambda_utils.Make

  (** Generates the lambda expression that throws the exception once we've
      determined that precomputing the array size has overflowed.  The check for
      overflow is done elsewhere, this just throws the exception
      unconditionally. *)
  let raise_overflow_exn ~loc =
    (* CR aspectorzabusky: Is this idiomatic?  Should the argument to [string]
       (a string constant) just get [Location.none] instead? *)
    let loc' = Debuginfo.Scoped_location.to_location loc in
    let slot =
      transl_extension_path
        loc
        Env.initial_safe_string
        Predef.path_invalid_argument
    in
    (* CR aspectorzabusky: Should I call [Translprim.event_after] here?
       [Translcore.asssert_failed] does (via a local intermediary). *)
    Lprim(Praise Raise_regular,
          [Lprim(Pmakeblock(0, Immutable, None),
                 [slot; (string ~loc:loc' "Array.make")],
                  (* CR aspectorzabusky: Is "Array.make" the right argument?
                     That's not *really* what's failing... *)
                 loc)],
          loc)

  (** [safe_mul_nonneg ~loc x y] generates the lambda expression that computes
      the product [x * y] of two nonnegative integers and fails if this
      overflowed *)
  let safe_mul_nonneg ~loc x y =
    let open (val Lambda_utils.int_ops ~loc) in
    let x, x_binding =
      Let_binding.make_var Strict Pintval "x"       x
    in
    let y, y_binding =
      Let_binding.make_var Strict Pintval "y"       y
    in
    let product, product_binding =
      Let_binding.make_var Alias  Pintval "product" (x * y)
    in
    Let_binding.let_all [x_binding; y_binding; product_binding]
      (Lifthenelse(y = l0 || product / y = x,
         product,
         raise_overflow_exn ~loc))

  (** [safe_product_nonneg ~loc xs] generates the lambda expression that
      computes the product of all the lambda terms in [xs] assuming they are all
      nonnegative integers, failing if any product overflows *)
  let safe_product_nonneg ~loc = function
    | (x :: xs) -> List.fold_left (safe_mul_nonneg ~loc) x xs
    | []        -> int 1
      (* The empty list case can't happen with list comprehensions; we could
         an error here instead of returning 1 *)

  module Let_bindings = struct
    type range =
      { start     : Let_binding.t
      ; stop      : Let_binding.t
      ; direction : direction_flag }

    type 'u array_iterator =
      | Range of ('u, range) Usage.if_reused
      | Array of { iter_arr : Let_binding.t
                 ; iter_len : ('u, Let_binding.t) Usage.if_reused }

    let range (type u)
          ~(start : (u, Let_binding.t) Usage.if_reused)
          ~(stop  : (u, Let_binding.t) Usage.if_reused)
          ~direction
        : u array_iterator =
      match start, stop with
      | Used_once, Used_once ->
          Range Used_once
      | Reusable start, Reusable stop ->
          Range (Reusable { start; stop; direction })

    let get (type u) : u array_iterator -> Let_binding.t list = function
      | Range (Reusable {start; stop; direction = _}) ->
          [start; stop]
      | Range Used_once ->
          []
      | Array {iter_arr; iter_len} ->
          iter_arr :: match iter_len with
                      | Reusable iter_len -> [iter_len]
                      | Used_once         -> []

    let get_all bindings = List.concat_map get bindings

    let size ~loc : Usage.many array_iterator -> lambda = function
      | Range (Reusable { start; stop; direction })  ->
          let open (val Lambda_utils.int_ops ~loc) in
          let start = Lvar start.id in
          let stop  = Lvar stop.id in
          let low, high = match direction with
            | Upto   -> start, stop
            | Downto -> stop,  start
          in
          Lifthenelse(low < high,
            (* The range has content *)
            (let range_size = Ident.create_local "range_size" in
             Llet(Alias, Pintval, range_size, (high - low) + l1,
               (* If the computed size of the range is nonpositive, there was
                  overflow.  (The zero case is checked for when we check to see
                  if the bounds are in the right order.) *)
               Lifthenelse(Lvar range_size > l0,
                 Lvar range_size,
                 raise_overflow_exn ~loc))),
            (* The range is empty *)
            l0)
      | Array { iter_arr = _; iter_len = Reusable iter_len } ->
          Lvar iter_len.id

    let total_size ~loc (iterators : Usage.many array_iterator list) =
      safe_product_nonneg ~loc (List.map (size ~loc) iterators)
  end
end

let transl_arr_iterator ~usage ~transl_exp ~scopes ~loc = function
  | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
      let transl_bound name bound =
        Let_binding.make_if_reused ~usage Strict Pintval
          name (transl_exp ~scopes bound)
      in
      let start, start_binding = transl_bound "start" start in
      let stop,  stop_binding  = transl_bound "stop"  stop  in
      let mk_iterator body =
        Lfor(ident, start, stop, direction, body)
      in
      mk_iterator, Precompute_array_size.Let_bindings.range
                     ~start:start_binding
                     ~stop:stop_binding
                     ~direction
  | Texp_comp_in { pattern; sequence = iter_arr } ->
      let iter_arr_var, iter_arr_binding =
        Let_binding.make_var Strict Pgenval
          "iter_arr" (transl_exp ~scopes iter_arr)
      in
      let iter_arr_kind = Typeopt.array_kind iter_arr in
      let iter_len, iter_len_binding =
        Let_binding.make_if_reused ~usage Alias Pintval
          "iter_len"
          (Lprim(Parraylength iter_arr_kind, [iter_arr_var], loc))
      in
      let iter_ix = Ident.create_local "iter_ix" in
      let mk_iterator body =
        let open (val Lambda_utils.int_ops ~loc) in
        (* for iter_ix = 0 to Array.length iter_arr - 1 ... *)
        Lfor(iter_ix, l0, iter_len - l1, Upto,
             Matching.for_let
               ~scopes
               pattern.pat_loc
               (Lprim(Parrayrefu iter_arr_kind,
                      [iter_arr_var; Lvar iter_ix],
                      loc))
               pattern
               body)
      in
      mk_iterator, Precompute_array_size.Let_bindings.Array
                     { iter_arr = iter_arr_binding
                     ; iter_len = iter_len_binding }

let transl_arr_binding
      ~transl_exp
      ~loc
      ~scopes
      { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  transl_arr_iterator ~transl_exp ~loc ~scopes comp_cb_iterator

let transl_nested_with_bindings transl =
  List.fold_left_map
    (fun whole_cps next ->
       let next_cps, bindings = transl next in
       (fun body -> whole_cps (next_cps body)), bindings)
    Fun.id

(* As [transl_nested_with_bindings], but we don't need to keep track of the
   generated let-bindings *)
let transl_nested transl =
  List.fold_left
    (fun whole_cps next ->
       let next_cps = transl next in
       fun body -> whole_cps (next_cps body))
    Fun.id

(* Separated out for the known fixed size case *)
let transl_arr_for_and_clause ~sizing ~transl_exp ~loc ~scopes =
  transl_nested_with_bindings
    (transl_arr_binding ~sizing ~transl_exp ~loc ~scopes)

let transl_arr_clause ~transl_exp ~loc ~scopes = function
  | Texp_comp_for bindings ->
      let transl_clause, var_bindings =
        transl_arr_for_and_clause
          ~sizing:Unknown_size
          ~transl_exp
          ~loc
          ~scopes
          bindings
      in
      fun body -> gen_bindings
                    (array_iterator_let_bindings var_bindings)
                    (transl_clause body)
  | Texp_comp_when cond ->
      fun body -> Lifthenelse(transl_exp ~scopes cond, body, lambda_unit)

(* A small power of two; this both "feels nice" and means that we only exceed
   [Sys.max_array_length] when it's time to do so, under the assumption that
   said limit is of the form 2^x-1. *)
let starting_resizable_array_size = 8

(* If the array comprehension is of the form

       [|BODY for ITER and ITER ... and ITER|]

   then we can compute the size of the resulting array before allocating it
   ([Fixed_size], which carries the expression that computes this size);
   otherwise, we cannot ([Unknown_size]), and we have to dynamically grow the
   array as we iterate and shrink it to size at the end.  In this latter case,
   we need to bind the array size to a mutable variable so it can be queried,
   and [Unknown_size] carries this variable name. *)
type array_sizing =
  | Fixed_size   of lambda
  | Unknown_size of Ident.t

type translated_clauses =
  { array_sizing       : array_sizing
  ; outer_bindings     : binding list
  ; make_comprehension : lambda -> lambda }

let transl_arr_clauses ~transl_exp ~loc ~scopes = function
  | [Texp_comp_for bindings] ->
      let transl_clause, var_bindings =
        transl_arr_for_and_clause
          ~sizing:Fixed_size
          ~transl_exp
          ~loc
          ~scopes
          bindings
      in
      let starting_size = transl_arr_fixed_bindings_size ~loc var_bindings in
      { array_sizing       = Fixed_size starting_size
      ; outer_bindings     = array_iterator_let_bindings var_bindings
      ; make_comprehension = transl_clause }
  | clauses ->
      let array_size, array_size_binding =
        id_binding
          Variable
          Pintval
          "array_size"
          (int starting_resizable_array_size)
      in
      let transl_clauses =
        transl_nested (transl_arr_clause ~transl_exp ~loc ~scopes) clauses
      in
      { array_sizing       = Unknown_size array_size
      ; outer_bindings     = [array_size_binding]
      ; make_comprehension = transl_clauses }

let make_array_prim ~loc size init =
  let prim =
    Primitive.simple ~name:"caml_make_vect" ~arity:2 ~alloc:true
  in
  Lprim (Pccall prim, [size; init], loc)

let make_floatarray_prim ~loc size =
  let prim =
    Primitive.simple ~name:"caml_make_float_vect" ~arity:1 ~alloc:true
  in
  Lprim (Pccall prim, [size], loc)

let array_append_prim ~loc arr1 arr2 =
  let prim =
    Primitive.simple ~name:"caml_array_append" ~arity:2 ~alloc:true
  in
  Lprim (Pccall prim, [arr1; arr2], loc)

let make_initial_resizable_array ~loc array_kind elt =
  Lprim(Pmakearray(array_kind, Mutable),
        Misc.replicate_list elt starting_resizable_array_size,
        loc)

let transl_arr_init_array ~loc ~array_kind ~array_sizing =
  (* There are three cases to consider for how we allocate the array.

     1. We are subject to the float array hack: The array kind is Pgenarray.  In
        this case, we create an immutable empty array as a Variable, since
        rather than being updated it will simply be overwritten once we have the
        first element.  This is the only time a fixed-size array needs to be a
        Variable, since it will be overwritten on the first iteration.
     2. The array is of fixed size and known array kind, in which case we use
        [caml_make_(float)vect] to create the array, and bind it as [StrictOpt]
        since it never needs to be overwritten to be resized.
     3. The array is of unknown size and known array kind, in which case we
        create a small array of default values using [Pmakearray] and bind it as
        a Variable so that it can be overwritten when its size needs to be
        doubled. *)
  let array_let_kind, array_value = match array_sizing, array_kind with
    (* Case 1: Float array hack difficulties *)
    | (Fixed_size _ | Unknown_size _), Pgenarray ->
        Variable, Lprim(Pmakearray(Pgenarray, Immutable), [], loc)
    (* Case 2: Fixed size, known array kind *)
    | Fixed_size size, (Pintarray | Paddrarray) ->
        StrictOpt, make_array_prim ~loc size (int 0)
    | Fixed_size size, Pfloatarray ->
        StrictOpt, make_floatarray_prim ~loc size
    (* Case 3: Unknown size, known array kind *)
    | Unknown_size _, (Pintarray | Paddrarray) ->
        Variable, make_initial_resizable_array ~loc array_kind (int 0)
    | Unknown_size _, Pfloatarray ->
        Variable, make_initial_resizable_array ~loc array_kind (float 0.)
  in
  id_binding array_let_kind Pgenval "array" array_value

(* Generate the code for the body of an array comprehension:
     1. Compute the next element
     2. Assign it (mutably) to the next element of the array
     3. Advance the index of the next element
   However, there's several pieces of complexity:
     (a) If the array size is not fixed, we have to check if the index has
         overflowed; if it has, we have to double the size of the array.  (The
         complex case corresponds to [array_sizing] being [Unknown_size].)
     (b) If the array kind is not statically known, we initially created an
         empty array; we have to check if we're on the first iteration and use
         the putative first element of the array as the placeholder value for
         every element of the array.  (The complex case corresponds to
         [array_kind] being [Pgenarray].)
     (c) If both (a) and (b) hold, we shouldn't bother checking for an
         overflowed index on the first loop iteration.
   The result is that we build the "set the element" behavior in three steps:
     i.   First, we build the raw "set the element unconditionally" expression
          ([set_element_raw]).
     ii.  Then, if necessary, we precede that with the resizing check;
          otherwise, we leave the raw behavior alone ([set_element_in_bounds]).
     iii. Then, if necessary, we check to see if we're on the first iteration
          and create the fresh array instead if so; otherwise, we leave the
          size-safe behavior alone ([set_element_known_kind_in_bounds]).
     iv.  Finally, we take the resulting safe element-setting behavior (which
          could be equal to the result from any of stages i--iii), and follow it
          up by advancing the index of the element to update.
*)
let transl_arr_body ~loc ~array_kind ~array_sizing ~array ~index ~body =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  (* CR aspectorzabusky: This used to use shadowing, but I think this is
     clearer? *)
  let set_element_raw elt =
    (* array.(index) <- elt *)
    Lprim(Parraysetu array_kind, [Lvar array; Lvar index; elt], loc)
      (* CR aspectorzabusky: Is [array_kind] safe here, since it could be
         [Pgenarray]?  Do we have to learn which it should be? *)
  in
  let set_element_in_bounds elt = match array_sizing with
    | Fixed_size _ ->
        set_element_raw elt
    | Unknown_size array_size ->
        Lsequence(
          (* Double the size of the array if it's time *)
          Lifthenelse(Lvar index < Lvar array_size,
            lambda_unit,
            Lsequence(
              Lassign(array_size, i 2 * Lvar array_size),
              (* This is probably not the optimal way to double the size of an
                 array, but it's good enough for now. *)
              Lassign(array,
                      array_append_prim ~loc (Lvar array) (Lvar array)))),
        set_element_raw elt)
  in
  let set_element_known_kind_in_bounds = match array_kind with
    | Pgenarray ->
        let is_first_iteration = (Lvar index = l0) in
        let elt = Ident.create_local "elt" in
        let make_array = match array_sizing with
          | Fixed_size size ->
              make_array_prim ~loc size (Lvar elt)
          | Unknown_size _ ->
              make_initial_resizable_array ~loc Pgenarray (Lvar elt)
        in
        (* CR aspectorzabusky: Is Pgenval safe here? *)
        Llet(Strict, Pgenval, elt, body,
             Lifthenelse(is_first_iteration,
               Lassign(array, make_array),
               set_element_in_bounds (Lvar elt)))
    | Pintarray | Paddrarray | Pfloatarray ->
        set_element_in_bounds body
  in
  Lsequence(
    set_element_known_kind_in_bounds,
    Lassign(index, Lvar index + l1))

(* CR aspectorzabusky: Should we move the [Primitive.simple] call outside of the
   function? *)
let sub_array_prim ~loc arr ~pos ~len =
  let prim_sub_arr =
    Primitive.simple ~name:"caml_array_sub" ~arity:3 ~alloc:true
  in
  Lprim (Pccall prim_sub_arr, [arr; pos; len], loc)

let transl_array_comprehension
      ~transl_exp ~scopes ~loc ~array_kind { comp_body; comp_clauses } =
  let { array_sizing; outer_bindings; make_comprehension } =
    transl_arr_clauses ~transl_exp ~scopes ~loc comp_clauses
  in
  let array, array_binding =
    transl_arr_init_array ~loc ~array_kind ~array_sizing
  in
  let index, index_var, index_binding =
    id_var_binding Variable Pintval "index" (int 0)
  in
  Binding.let_all
    (outer_bindings @ [array_binding; index_binding])
    (Lsequence(
       make_comprehension
         (transl_arr_body
            ~loc
            ~array_kind
            ~array_sizing
            ~array
            ~index
            ~body:(transl_exp ~scopes comp_body)),
       match array_sizing with
       | Fixed_size _ ->
           Lvar array
       | Unknown_size _ ->
           (sub_array_prim ~loc (Lvar array) ~pos:(int 0) ~len:index_var)))

let transl_list_comprehension ~transl_exp:_ ~scopes:_ ~loc:_ _comprehension =
  lambda_unit

(*
let in_comp_prim () = Lambda.transl_prim "CamlinternalComprehension" "map_cons"

let comp_rev () = Lambda.transl_prim "CamlinternalComprehension" "rev"

let transl_list_comp type_comp body acc_var mats ~transl_exp ~scopes ~loc =
  let new_acc = Ident.create_local "acc" in
  let param, pval, args, func, body, mats =
    match type_comp with
    | From_to (param, _,e2,e3, dir) ->
      let pval = Pintval in
      let from_var = Ident.create_local "from" in
      let to_var = Ident.create_local "to_" in
      let args = [Lvar(from_var); Lvar(to_var); Lvar(new_acc)] in
      let func = from_to_comp_prim ~dir in
      let mats =
        (from_var, transl_exp ~scopes e2)::(to_var, transl_exp ~scopes e3)::mats
      in
      param, pval, args, func, body, mats
    | In (pat, in_) ->
      let pat_id = Ident.create_local "pat" in
      let pval = Typeopt.value_kind pat.pat_env pat.pat_type in
      let in_var = Ident.create_local "in_var" in
      let args = [Lvar(in_var); Lvar(new_acc)] in
      let func = in_comp_prim () in
      let body =
        Matching.for_let ~scopes pat.pat_loc (Lvar(pat_id)) pat body
      in
      let mats = (in_var, transl_exp ~scopes in_)::mats in
      pat_id , pval, args, func, body, mats
  in
  let fn =
    Lfunction {kind = Curried;
              params= [param, pval; acc_var, Pgenval];
              return = Pgenval;
              attr = default_function_attribute;
              loc = loc;
              body = body}
  in
  Lapply{
    ap_loc=loc;
    ap_func=func;
    ap_args= fn::args;
    ap_tailcall=Default_tailcall;
    ap_inlined=Default_inlined;
    ap_specialised=Default_specialise;
    ap_probe=None;
  }, new_acc, mats

let transl_list_comprehension ~transl_exp ~loc ~scopes body blocks =
  let acc_var = Ident.create_local "acc" in
  let bdy =
    Lprim(
      Pmakeblock(0, Immutable, None),
      [(transl_exp ~scopes  body); Lvar(acc_var)], loc)
  in
  let res_list, res_var = List.fold_left
    (fun (body, acc_var)  block ->
      let body =
        match block.guard with
        | None -> body
        | Some guard ->
          Lifthenelse((transl_exp ~scopes  guard), body, Lvar(acc_var))
      in
      let body, acc_var, materialize =
        List.fold_left
          (fun (body, acc_var, mats) el ->
            transl_list_comp ~transl_exp ~scopes ~loc el body acc_var mats)
          (body, acc_var, []) block.clauses
        in
        let body = List.fold_right (fun (id, arr) body ->
          Llet(Strict, Pgenval, id, arr, body))
          materialize body
        in
        body, acc_var)
    (bdy, acc_var) blocks
  in
  Llet(Alias, Pintval, res_var, int 0, (*Empty list.*)
    Lapply{
        ap_loc=loc;
        ap_func=comp_rev ();
        ap_args=[res_list];
        ap_tailcall=Default_tailcall;
        ap_inlined=Default_inlined;
        ap_specialised=Default_specialise;
        ap_probe=None;
      })

(*******************************************************************************)

(* Translate a clause into some initialising bindings, a variable
   that will be bound to the number of iterations in the clause by
   those bindings, and lambda code that performs the iterations. *)
let transl_arr_clause ~transl_exp ~scopes ~loc clause body =
  let len_var = Ident.create_local "len_var" in
  let bindings, for_ =
    match clause with
    | In (pat , e2) ->
        let in_var = Ident.create_local "in_var" in
        let in_kind = Typeopt.array_kind e2 in
        let in_binding =
          binding Strict Pgenval in_var (transl_exp ~scopes e2)
        in
        let len_binding =
          let init = Lprim( (Parraylength(in_kind)), [Lvar(in_var)], loc) in
          binding Alias Pintval len_var init
        in
        let index = Ident.create_local "index" in
        let for_ =
          Lfor(index, (int 0), Lprim(Psubint, [Lvar(len_var); int 1], loc) , Upto,
            Matching.for_let ~scopes pat.pat_loc
              (Lprim(Parrayrefu(in_kind),
                     [Lvar(in_var); Lvar(index)], loc)) pat body)
        in
        [in_binding; len_binding], for_
    | From_to(id, _, e2, e3, dir) ->
        let from_var = Ident.create_local "from" in
        let from_binding =
          binding Strict Pintval from_var (transl_exp ~scopes e2)
        in
        let to_var = Ident.create_local "to" in
        let to_binding =
          binding Strict Pintval to_var (transl_exp ~scopes e3)
        in
        let low, high =
          match dir with
          | Upto -> Lvar from_var, Lvar to_var
          | Downto -> Lvar to_var, Lvar from_var
        in
        let len_binding =
          let init =
            Lprim(Psubint, [Lprim(Paddint, [high; int 1], loc); low], loc)
          in
          binding Alias Pintval len_var init
        in
        let for_ = Lfor(id, Lvar from_var, Lvar to_var, dir, body) in
        [from_binding; to_binding; len_binding], for_
  in
  bindings, len_var, for_

(* Generate code to iterate over a comprehension block, along with some
   initialising bindings.  The bindings will also bind the given
   [length_var] ident to the total number of iterations in the
   block. *)
let iterate_arr_block ~transl_exp ~loc ~scopes
      {clauses; guard} length_var body =
  let body =
    match guard with
    | None -> body
    | Some guard ->
      Lifthenelse(transl_exp ~scopes guard, body, lambda_unit)
  in
  let body, length_opt, bindings =
    List.fold_left
      (fun (body, length, bindings) clause ->
         let new_bindings, new_length_var, body =
           transl_arr_clause ~transl_exp ~scopes ~loc clause body
         in
         let rev_bindings = new_bindings @ bindings in
         let length =
           match length with
           | None -> Lvar new_length_var
           | Some length ->
               Lprim(Pmulint, [Lvar new_length_var; length], loc)
         in
         body, Some length, rev_bindings)
      (body, None, []) clauses
  in
  let length = Option.value length_opt ~default:(int 0) in
  let length_binding = binding Alias Pintval length_var length in
  let bindings = List.append bindings [length_binding] in
  bindings, body
*)
