open Lambda

let comprehension ~transl_exp:_ ~scopes:_ ~loc:_ _comprehension =
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
