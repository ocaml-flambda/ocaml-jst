open Lambda
open Typedtree
open Asttypes

[@@@warning "-32"]

let int n = Lconst (Const_base (Const_int n))

type binding =
  { let_kind : let_kind;
    value_kind : value_kind;
    var : Ident.t;
    init : lambda }

let binding let_kind value_kind var init =
  {let_kind; value_kind; var; init}

let gen_binding {let_kind; value_kind; var; init} body =
  Llet(let_kind, value_kind, var, init, body)

let gen_bindings bindings body =
  List.fold_right gen_binding bindings body

module type Lambda_int_ops = sig
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

let lunless cond body = Lifthenelse(cond, lambda_unit, body)

let safe_range_size ~loc ~low ~high =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  let range_size = Ident.create_local "range_size" in
  Lifthenelse(low <= high,
    Llet(Alias, Pintval,
         range_size, (high - low) + l1,
         Lifthenelse(Lvar range_size >= l0,
           Lvar range_size,
           Lprim(Praise Raise_regular, [], loc))),
    l0)

(* [safe_mul_assign ~loc ~product x y] generates lambda code that computes
   [product := x * y] but fails if the multiplication overflowed *)
let safe_mul_assign ~loc ~product x y =
  let (module O) = lambda_int_ops ~loc in
  let open O in
  Lsequence(
    Lassign(product, x * y),
    Lifthenelse(y = i 0 || Lvar product / y = x,
                lambda_unit,
                Lprim(Praise Raise_regular, [], loc)))

let transl_arr_iterator ~transl_exp ~scopes ~loc iterator =
  let len_var        = Ident.create_local "len_var" in
  let mk_len_binding = binding Alias Pintval len_var in
  let bindings, mk_iterator = match iterator with
    | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
        let transl_bound name bound =
          let var = Ident.create_local name in
          Lvar var, binding Strict Pintval var (transl_exp ~scopes bound)
        in
        let start_var, start_binding = transl_bound "start" start in
        let stop_var,  stop_binding  = transl_bound "stop"  stop  in
        let len_binding =
          let low, high = match direction with
            | Upto   -> start_var, stop_var
            | Downto -> stop_var,  start_var
          in
          mk_len_binding (safe_range_size ~loc ~low ~high)
        in
        let mk_iterator body =
          Lfor(ident, start_var, stop_var, direction, body)
        in
        [start_binding; stop_binding; len_binding], mk_iterator
    | Texp_comp_in { pattern; sequence = arr } ->
        let arr_var     = Ident.create_local "arr_var" in
        let arr_kind    = Typeopt.array_kind arr in
        let arr_binding = binding Strict Pgenval arr_var (transl_exp ~scopes arr) in
        let len_binding =
          mk_len_binding (Lprim(Parraylength arr_kind, [Lvar arr_var], loc))
        in
        let index = Ident.create_local "index" in
        let mk_iterator body =
          (* for index = 0 to Array.length arr - 1 ... *)
          Lfor(index, int 0, Lprim(Psubint, [Lvar len_var; int 1], loc), Upto,
               Matching.for_let
                 ~scopes
                 pattern.pat_loc
                 (Lprim(Parrayrefu arr_kind, [Lvar arr_var; Lvar index], loc))
                 pattern
                 body)
        in
        [arr_binding; len_binding], mk_iterator
  in
  bindings, len_var, mk_iterator

let transl_arr_binding
      ~transl_exp
      ~loc
      ~scopes
      { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  transl_arr_iterator ~transl_exp ~loc ~scopes comp_cb_iterator

let transl_arr_clause ~transl_exp ~loc ~scopes length_var = function
  | Texp_comp_for bindings ->
      let bindings, length_opt, with_body =
        List.fold_left
          (fun (bindings, length, with_body) binding ->
             let new_bindings, length_var, mk_iterator =
               transl_arr_binding ~transl_exp ~loc ~scopes binding
             in
             let bindings = new_bindings @ bindings in
             let length = match length with
               | None        -> Lvar length_var
               | Some length -> Lprim(Pmulint, [Lvar length_var; length], loc)
             in
             let with_body body = mk_iterator (with_body body) in
             bindings, Some length, with_body)
          ([], None, Fun.id)
          bindings
      in
      let length = Option.value length_opt ~default:(int 0) in
      let length_binding = binding Alias Pintval length_var length in
      let bindings = bindings @ [length_binding] in
      bindings, with_body
  | Texp_comp_when cond ->
      [], fun body -> Lifthenelse(transl_exp ~scopes cond, body, lambda_unit)

let transl_arr_clauses ~transl_exp ~loc ~scopes length_var =
  List.fold_left
    (fun (bindings, all_clauses_k) clause ->
       let new_bindings, with_body =
         transl_arr_clause ~transl_exp ~loc ~scopes length_var clause
       in
       bindings @ new_bindings, fun body -> all_clauses_k (with_body body))
    ([], Fun.id)

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

let blit_array_prim ~loc src src_pos dst dst_pos len =
  let prim_blit_arr =
    Primitive.simple ~name:"caml_array_blit" ~arity:5 ~alloc:true
  in
  Lprim (Pccall prim_blit_arr, [src; src_pos; dst; dst_pos; len], loc)

(* Generate binding to make an "uninitialized" array *)
let make_array ~loc ~kind ~size ~array =
  match kind with
  | Pgenarray ->
      (* This array can be Immutable since it is empty and will later be
         replaced when an example value (to create the array) is known.
         That is also why the biding is a Variable. *)
      let init = Lprim(Pmakearray(Pgenarray, Immutable), [], loc) in
      binding Variable Pgenval array init
  | Pintarray | Paddrarray ->
      let init = make_array_prim ~loc size (int 0) in
      binding Strict Pgenval array init
  | Pfloatarray ->
      let init = make_floatarray_prim ~loc size in
      binding Strict Pgenval array init

(* Generate code to initialise an element of an "uninitialised" array *)
let init_array_elem ~loc ~kind ~size ~array ~index ~value =
  let set_elem =
    Lprim(Parraysetu kind, [Lvar array; Lvar index; Lvar value], loc)
  in
  match kind with
  | Pgenarray ->
      let is_first_iteration =
        Lprim(Pintcomp Ceq, [Lvar index; int 0], loc)
      in
      let make_array =
        Lassign(array, make_array_prim ~loc size (Lvar value))
      in
      Lifthenelse(is_first_iteration, make_array, set_elem)
  | Pintarray | Paddrarray | Pfloatarray -> set_elem

(* Generate code to blit elements into an "uninitialised" array *)
let init_array_elems ~loc ~kind ~size ~array ~index ~src ~len =
  let blit =
    blit_array_prim ~loc (Lvar src) (int 0) (Lvar array) (Lvar index) (Lvar len)
  in
  match kind with
  | Pgenarray ->
      let is_first_iteration =
        Lprim(Pintcomp Ceq, [Lvar index; int 0], loc)
      in
      let is_not_empty =
        Lprim(Pintcomp Cne, [Lvar len; int 0], loc)
      in
      let first_elem =
        Lprim(Parrayrefu kind, [Lvar src; int 0], loc)
      in
      let make_array =
        Lassign(array, make_array_prim ~loc size first_elem)
      in
      Lsequence(
        Lifthenelse(is_first_iteration,
          Lifthenelse(is_not_empty, make_array, lambda_unit),
          lambda_unit),
        blit)
  | Pintarray | Paddrarray | Pfloatarray -> blit

(* Binding for a counter *)
let make_counter counter =
  binding Variable Pintval counter (int 0)

(* Code to increment a counter *)
let increment_counter ~loc counter step =
  Lassign(counter, Lprim(Paddint, [Lvar counter; step], loc))

let blarp ~loc ~array_kind ~array_size ~array ~index ~body =
  Lsequence(
    Lifthenelse(
      Lprim(Pintcomp Clt, [Lvar index; array_size], loc),
      lambda_unit,
      Lassign(array, (* double it *) Lvar array)),
    Lprim(Parraysetu array_kind, [Lvar array; Lvar index; body], loc))


let rec go ~loc ~new_size ~prev_size ~size = function
  | [] -> prev_size, lambda_unit (* how do I remove this? *)
  | arr_size :: arr_sizes ->
      let final_size, multiply_rest =
        go ~loc ~new_size:prev_size ~prev_size:new_size ~size arr_sizes
      in
      final_size,
      Lsequence(
        Lassign(size, arr_size),
        Lsequence(
          safe_mul_assign ~loc ~product:new_size (Lvar prev_size) (Lvar size),
          multiply_rest))

(* let combine ~loc ~total_size = function
 *   | [] ->
 *       Misc.fatal_error
 *         "Comprehensions must have at least one clause, but translation into \
 *          found an array comprehension with no clauses"
 *   | [size] ->
 *       (* Avoids creating extra variables; however, the latter case would still
 *          work, this is just an optimization *)
 *       Lassign(total_size, size)
 *   | size :: sizes ->
 *       let size_var = Ident.create_local "size" in
 *       List
 *         Llet(Alias, Pintval, size_var, size,
 *              total_size
 *            Lassign(total_size, size)
 *
 *
 * total_size_1 = length arr1
 * size = length arr2
 * total_size_2 = total_size_1 * size
 * size = length arr3
 * total_size_1 = total_size_2 * size
 * size = length arr4
 * total_size_2 = total_size_1 * size *)

let transl_array_comprehension
      ~transl_exp ~scopes ~loc ~array_kind { comp_body; comp_clauses } =
  let starting_size = 10 (* CR aspectorzabusky: pick deliberately *) in
  let array_size = Ident.create_local "array_size" in
  let index      = Ident.create_local "index" in
  let array      = Ident.create_local "array" in
  let comprehension_bindings =
    [ binding Alias    Pintval array_size (int starting_size)
    ; binding Variable Pintval index      (int 0)
    ; binding Variable Pgenval array
        (Lprim(Pmakearray(array_kind, Mutable),
               Misc.replicate_list (int 0) starting_size,
               loc))
    ]
  in
  let clause_bindings, make_comprehension =
    transl_arr_clauses ~transl_exp ~scopes ~loc array_size comp_clauses
  in
  gen_bindings
    (comprehension_bindings @ clause_bindings)
    (Lsequence(
       make_comprehension
         (blarp ~loc ~array_kind ~array_size:(Lvar array_size) ~array ~index ~body:(transl_exp ~scopes comp_body)),
       (* CR aspectorzabusky: shrink array *)
       Lvar array))

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
