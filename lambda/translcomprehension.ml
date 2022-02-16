open Lambda
open Typedtree
open Asttypes

type binding =
  { let_kind : let_kind;
    value_kind : value_kind;
    var : Ident.t;
    init : lambda }

let binding let_kind value_kind var init =
  {let_kind; value_kind; var; init}

let id_binding let_kind value_kind name init =
  let id = Ident.create_local name in
  id, binding let_kind value_kind id init

let id_var_binding let_kind value_kind name init =
  let id, binding = id_binding let_kind value_kind name init in
  id, Lvar id, binding

let var_binding let_kind value_kind name init =
  let _id, var, binding = id_var_binding let_kind value_kind name init in
  var, binding

let gen_binding {let_kind; value_kind; var; init} body =
  Llet(let_kind, value_kind, var, init, body)

let gen_bindings bindings body =
  List.fold_right gen_binding bindings body

let int n = Lconst (const_int n)

let float f = Lconst (Const_base (Const_float (Float.to_string f)))

module type Lambda_int_ops = sig
  [@@@warning "-32"]

  val ( + ) : lambda -> lambda -> lambda
  val ( - ) : lambda -> lambda -> lambda
  val ( * ) : lambda -> lambda -> lambda
  val ( / ) : lambda -> lambda -> lambda

  val ( = )  : lambda -> lambda -> lambda
  val ( <> ) : lambda -> lambda -> lambda
  val ( < )  : lambda -> lambda -> lambda
  val ( > )  : lambda -> lambda -> lambda
  val ( <= ) : lambda -> lambda -> lambda
  val ( >= ) : lambda -> lambda -> lambda

  val ( && ) : lambda -> lambda -> lambda
  val ( || ) : lambda -> lambda -> lambda

  val l0 : lambda
  val l1 : lambda
  val i  : int -> lambda
end

let lambda_int_ops ~loc : (module Lambda_int_ops) = (module struct
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

(* CR aspectorzabusky: Should these hold less information and then have us
   construct the [binding] later? *)
type array_iterator_let_bindings =
  | Range_let_bindings of
      { start_binding : binding
      ; stop_binding  : binding
      ; direction     : direction_flag }
  | Array_let_bindings of
      { iter_arr_binding : binding
      ; iter_len_binding : binding }

let array_iterator_let_bindings =
  List.concat_map
    (function
      | Range_let_bindings { start_binding; stop_binding } ->
          [start_binding; stop_binding]
      | Array_let_bindings { iter_arr_binding; iter_len_binding } ->
          [iter_arr_binding; iter_len_binding])

(* CR aspectorzabusky: Raise something real *)
let asz_bad_exn ~(loc : Lambda.scoped_location) =
  let scopes = Debuginfo.Scoped_location.empty_scopes in
  let to_location = Debuginfo.Scoped_location.to_location in
  let slot =
    transl_extension_path Loc_unknown
      Env.initial_safe_string Predef.path_assert_failure
  in
  let (fname, line, char) =
    "FNAME", 42, 666
  in
  let uloc = to_location loc in
  let event_after ~scopes:_ _exp lam =
    lam
  in
  Lprim(Praise Raise_regular, [event_after ~scopes lambda_unit
    (Lprim(Pmakeblock(0, Immutable, None),
          [slot;
           Lconst(Const_block(0,
              [Const_base(Const_string (fname, uloc, None));
               Const_base(Const_int line);
               Const_base(Const_int char)]))], loc))], loc)


let transl_arr_fixed_binding_size ~loc = function
  | Range_let_bindings { start_binding; stop_binding; direction }  ->
      let (module O) = lambda_int_ops ~loc in
      let open O in
      let start = Lvar start_binding.var in
      let stop  = Lvar stop_binding.var in
      let low, high = match direction with
        | Upto   -> start, stop
        | Downto -> stop,  start
      in
      Lifthenelse(low < high,
        (* The range has content *)
        (let range_size = Ident.create_local "range_size" in
         Llet(Alias, Pintval, range_size, (high - low) + l1,
           (* If the computed size of the range is nonpositive, there was
              overflow.  (The zero case is checked for when we check to see if
              the bounds are in the right order.) *)
           Lifthenelse(Lvar range_size > l0,
             Lvar range_size,
             Lprim(Praise Raise_regular, [asz_bad_exn ~loc], loc)))),
        (* The range is empty *)
        int 0)
  | Array_let_bindings { iter_arr_binding = _; iter_len_binding } ->
      Lvar iter_len_binding.var

(* [safe_mul_nonneg ~loc x y] computes the product [x * y] of two nonnegative
   integers and fails if this overflowed *)
let safe_mul ~loc x y =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  let x,       x_binding       = var_binding Strict Pintval "x"       x       in
  let y,       y_binding       = var_binding Strict Pintval "y"       y       in
  let product, product_binding = var_binding Alias  Pintval "product" (x * y) in
  gen_bindings [x_binding; y_binding; product_binding]
    (Lifthenelse(y = l0 || product / y = x,
       product,
       Lprim(Praise Raise_regular, [asz_bad_exn ~loc], loc)))

(* [safe_product_nonneg ~loc xs] computes the product of all the lambda terms in
   [xs] assuming they are all nonnegative integers, failing if any product
   overflows *)
let safe_product_nonneg ~loc = function
  | (x :: xs) -> List.fold_left (safe_mul ~loc) x xs
  | []        -> int 1
    (* The empty list case can't happen with list comprehensions; we could raise
       an error here instead of returning 1 *)

let transl_arr_fixed_bindings_size ~loc iterators =
  safe_product_nonneg ~loc
    (List.map (transl_arr_fixed_binding_size ~loc) iterators)

let transl_arr_iterator ~transl_exp ~scopes ~loc = function
  | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
      let transl_bound name bound =
        var_binding Strict Pintval name (transl_exp ~scopes bound)
      in
      let start_var, start_binding = transl_bound "start" start in
      let stop_var,  stop_binding  = transl_bound "stop"  stop  in
      let mk_iterator body =
        Lfor(ident, start_var, stop_var, direction, body)
      in
      mk_iterator, Range_let_bindings { start_binding; stop_binding; direction }
  | Texp_comp_in { pattern; sequence = iter_arr } ->
      let iter_arr_var, iter_arr_binding =
        var_binding Strict Pgenval "iter_arr" (transl_exp ~scopes iter_arr)
      in
      let iter_arr_kind = Typeopt.array_kind iter_arr in
      let iter_len_var, iter_len_binding =
        var_binding Alias Pintval
          "iter_len"
          (Lprim(Parraylength iter_arr_kind, [iter_arr_var], loc))
      in
      let iter_ix = Ident.create_local "iter_ix" in
      let mk_iterator body =
        (* for iter_ix = 0 to Array.length iter_arr - 1 ... *)
        Lfor(iter_ix, int 0, Lprim(Psubint, [iter_len_var; int 1], loc), Upto,
             Matching.for_let
               ~scopes
               pattern.pat_loc
               (Lprim(Parrayrefu iter_arr_kind,
                      [iter_arr_var; Lvar iter_ix],
                      loc))
               pattern
               body)
      in
      mk_iterator, Array_let_bindings { iter_arr_binding; iter_len_binding }

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
let transl_arr_for_and_clause ~transl_exp ~loc ~scopes =
  transl_nested_with_bindings (transl_arr_binding ~transl_exp ~loc ~scopes)

let transl_arr_clause ~transl_exp ~loc ~scopes = function
  | Texp_comp_for bindings ->
      let transl_clause, var_bindings =
        transl_arr_for_and_clause ~transl_exp ~loc ~scopes bindings
      in fun body -> gen_bindings
                       (array_iterator_let_bindings var_bindings)
                       (transl_clause body)
  | Texp_comp_when cond ->
      fun body -> Lifthenelse(transl_exp ~scopes cond, body, lambda_unit)

(* A small power of two *)
let starting_resizable_array_size = 8

(* If the array comprehension is of the form

       [|BODY for ITER and ITER ... and ITER|]

   then we can compute the size of the resulting array before allocating it
   ([Fixed_size], which carries the expression that computes this size);
   otherwise, we cannot ([Unknown_size]), and we have to dynamically grow the
   array as we iterate and shrink it to size at the end. *)
type array_sizing =
  | Fixed_size of lambda
  | Unknown_size

type translated_clauses =
  { array_sizing       : array_sizing
  ; outer_bindings     : binding list
  ; make_comprehension : lambda -> lambda }
  (* [outer_bindings] is nonempty iff [array_sizing] is [Fixed_size _]; however,
     we pass around [Fixed_size] too much for me to want to include it in
     [array_sizing]. *)

let transl_arr_clauses ~transl_exp ~loc ~scopes = function
  | [Texp_comp_for bindings] ->
      let transl_clause, var_bindings =
        transl_arr_for_and_clause ~transl_exp ~loc ~scopes bindings
      in
      let starting_size = transl_arr_fixed_bindings_size ~loc var_bindings in
      { array_sizing       = Fixed_size starting_size
      ; outer_bindings     = array_iterator_let_bindings var_bindings
      ; make_comprehension = transl_clause }
  | clauses ->
      let transl_clauses =
        transl_nested (transl_arr_clause ~transl_exp ~loc ~scopes) clauses
      in
      { array_sizing       = Unknown_size
      ; outer_bindings     = []
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

type transl_arr_init_array =
  { array_size     : Ident.t
  ; array          : Ident.t
  ; array_bindings : binding list }

let transl_arr_init_array ~loc ~array_kind ~array_sizing =
  let array_size_let_kind, array_size_value = match array_sizing with
    | Fixed_size size -> Alias,    size
    | Unknown_size    -> Variable, int starting_resizable_array_size
  in
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
    | (Fixed_size _ | Unknown_size), Pgenarray ->
        Variable, Lprim(Pmakearray(Pgenarray, Immutable), [], loc)
    (* Case 2: Fixed size, known array kind *)
    | Fixed_size size, (Pintarray | Paddrarray) ->
        StrictOpt, make_array_prim ~loc size (int 0)
    | Fixed_size size, Pfloatarray ->
        StrictOpt, make_floatarray_prim ~loc size
    (* Case 3: Unknown size, known array kind *)
    | Unknown_size, (Pintarray | Paddrarray) ->
        Variable, make_initial_resizable_array ~loc array_kind (int 0)
    | Unknown_size, Pfloatarray ->
        Variable, make_initial_resizable_array ~loc array_kind (float 0.)
  in
  let array_size, array_size_binding =
    id_binding array_size_let_kind Pintval "array_size" array_size_value
  in
  let array, array_binding =
    id_binding array_let_kind Pgenval "array" array_value
  in
  { array_size; array; array_bindings = [ array_size_binding; array_binding] }

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
let transl_arr_body
      ~loc ~array_kind ~array_sizing ~array_size ~array ~index ~body
  =
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
    | Unknown_size ->
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
          | Fixed_size _ ->
              make_array_prim ~loc (Lvar array_size) (Lvar elt)
          | Unknown_size ->
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
  let { array; array_size; array_bindings } =
    transl_arr_init_array ~loc ~array_kind ~array_sizing
  in
  let index, index_var, index_binding =
    id_var_binding Variable Pintval "index" (int 0)
  in
  gen_bindings
    (outer_bindings @ array_bindings @ [index_binding])
    (Lsequence(
       make_comprehension
         (transl_arr_body
            ~loc
            ~array_kind
            ~array_size
            ~array_sizing
            ~array
            ~index
            ~body:(transl_exp ~scopes comp_body)),
       match array_sizing with
       | Fixed_size _ ->
           Lvar array
       | Unknown_size ->
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
