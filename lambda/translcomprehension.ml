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

let id_var_binding let_kind value_kind name init =
  let id = Ident.create_local name in
  id, Lvar id, binding let_kind value_kind id init

let var_binding let_kind value_kind name init =
  let _id, var, binding = id_var_binding let_kind value_kind name init in
  var, binding

let gen_binding {let_kind; value_kind; var; init} body =
  Llet(let_kind, value_kind, var, init, body)

let gen_bindings bindings body =
  List.fold_right gen_binding bindings body

let int n = Lconst (const_int n)

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

(* CR aspectorzabusky: Raise something real *)
let asz_bad_exn = int 737

(* CR aspectorzabusky: I don't think these range checks are correct *)
        (* let len_binding =
         *   let low, high = match direction with
         *     | Upto   -> start_var, stop_var
         *     | Downto -> stop_var,  start_var
         *   in
         *   mk_len_binding (safe_range_size ~loc ~low ~high)
         * in *)
let safe_range_size ~loc ~low ~high =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  let range_size = Ident.create_local "range_size" in
  Lifthenelse(low <= high,
    Llet(Alias, Pintval,
         range_size, (high - low) + l1,
         Lifthenelse(Lvar range_size >= l0,
           Lvar range_size,
           Lprim(Praise Raise_regular, [asz_bad_exn], loc))),
    l0)
let _asz = safe_range_size

(* [safe_mul_assign ~loc ~product x y] generates lambda code that computes
   [product := x * y] but fails if the multiplication overflowed *)
let safe_mul_assign ~loc ~product x y =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  Lsequence(
    Lassign(product, x * y),
    Lifthenelse(y = i 0 || Lvar product / y = x,
                lambda_unit,
                Lprim(Praise Raise_regular, [asz_bad_exn], loc)))
let _asz = safe_mul_assign

let transl_arr_iterator ~transl_exp ~scopes ~loc iterator =
  let bindings, mk_iterator = match iterator with
    | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
        let transl_bound name bound =
          var_binding Strict Pintval name (transl_exp ~scopes bound)
        in
        let start_var, start_binding = transl_bound "start" start in
        let stop_var,  stop_binding  = transl_bound "stop"  stop  in
        let mk_iterator body =
          Lfor(ident, start_var, stop_var, direction, body)
        in
        [start_binding; stop_binding], mk_iterator
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
        [iter_arr_binding; iter_len_binding], mk_iterator
  in
  fun body -> gen_bindings bindings (mk_iterator body)

let transl_arr_binding
      ~transl_exp
      ~loc
      ~scopes
      { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  transl_arr_iterator ~transl_exp ~loc ~scopes comp_cb_iterator

let transl_nested transl =
  List.fold_left
    (fun whole_cps next ->
       let next_cps = transl next in
       fun body -> whole_cps (next_cps body))
    Fun.id

let transl_arr_clause ~transl_exp ~loc ~scopes = function
  | Texp_comp_for bindings ->
      transl_nested (transl_arr_binding ~transl_exp ~loc ~scopes) bindings
  | Texp_comp_when cond ->
      fun body -> Lifthenelse(transl_exp ~scopes cond, body, lambda_unit)

let transl_arr_clauses ~transl_exp ~loc ~scopes =
  transl_nested (transl_arr_clause ~transl_exp ~loc ~scopes)

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

(* Generate binding to make an "uninitialized" array *)
let make_uninitialized_array ~loc ~array_kind ~size =
  match array_kind with
  | Pgenarray ->
      (* This array can be Immutable since it is empty and will later be
         replaced when an example value (to create the array) is known. *)
      Lprim(Pmakearray(Pgenarray, Immutable), [], loc)
  | Pintarray | Paddrarray ->
      make_array_prim ~loc size (int 0)
  | Pfloatarray ->
      make_floatarray_prim ~loc size

type array_size_behavior =
  | Static_size
  | Resizable

(* Generate the code for the body of an array comprehension:
     1. Compute the next element
     2. Assign it (mutably) to the next element of the array
     3. Advance the index of the next element
   However, there's several pieces of complexity:
     (a) If the array size is not statically known, we have to check if the
         index has overflowed; if it has, we have to double the size of the
         array.  (The complex case corresponds to [array_size_behavior] being
         [Resizable].)
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
      ~loc ~array_kind ~array_size_behavior ~array_size ~array ~index ~body
  =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  (* CR aspectorzabusky: This used to use shadowing, but I think this is
     clearer? *)
  let set_element_raw =
    (* array.(index) <- body *)
    Lprim(Parraysetu array_kind, [Lvar array; Lvar index; body], loc)
  in
  let set_element_in_bounds = match array_size_behavior with
    | Static_size ->
        set_element_raw
    | Resizable ->
        Lsequence(
          (* Double the size of the array if it's time *)
          Lifthenelse(Lvar index < Lvar array_size,
            lambda_unit,
            Lsequence(
              Lassign(array_size, i 2 * Lvar array_size),
              (* CR aspectorzabusky: Is this the best way to double the size of
                 an array? *)
              Lassign(array,
                      array_append_prim ~loc (Lvar array) (Lvar array)))),
        set_element_raw)
  in
  let set_element_known_kind_in_bounds = match array_kind with
    | Pgenarray ->
        let is_first_iteration = (Lvar index = l0) in
        (* CR aspectorzabusky: Why doesn't this check to see if we have a float
           array? *)
        let make_array =
          Lassign(array, make_array_prim ~loc (Lvar array_size) body)
        in
        Lifthenelse(is_first_iteration, make_array, set_element_in_bounds)
    | Pintarray | Paddrarray | Pfloatarray ->
        set_element_in_bounds
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
  let starting_size = 10 (* CR aspectorzabusky: pick deliberately *) in
  let array_size = Ident.create_local "array_size" in
  let index      = Ident.create_local "index" in
  let array      = Ident.create_local "array" in
  let comprehension_bindings =
    [ binding Variable Pintval array_size (int starting_size)
    ; binding Variable Pintval index      (int 0)
    ; binding Variable Pgenval array
        (make_uninitialized_array ~loc ~array_kind ~size:(Lvar array_size))
    ]
  in
  let make_comprehension =
    transl_arr_clauses ~transl_exp ~scopes ~loc comp_clauses
  in
  gen_bindings
    comprehension_bindings
    (Lsequence(
       make_comprehension
         (transl_arr_body
            ~loc
            ~array_kind
            ~array_size
            ~array_size_behavior:(if false then Static_size else Resizable)
            ~array
            ~index
            ~body:(transl_exp ~scopes comp_body)),
       (sub_array_prim ~loc (Lvar array) ~pos:(int 0) ~len:(Lvar index))))

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
