(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Translation from typed abstract syntax to lambda terms,
   for the core language *)

open Misc
open Asttypes
open Primitive
open Types
open Typedtree
open Typeopt
open Lambda
open Debuginfo.Scoped_location

type error =
    Free_super_var
  | Unreachable_reached

exception Error of Location.t * error

let use_dup_for_constant_arrays_bigger_than = 4

(* Forward declaration -- to be filled in by Translmod.transl_module *)
let transl_module =
  ref((fun ~scopes:_ _cc _rootpath _modl -> assert false) :
      scopes:scopes -> module_coercion -> Longident.t option ->
      module_expr -> lambda)

let transl_object =
  ref (fun ~scopes:_ _id _s _cl -> assert false :
       scopes:scopes -> Ident.t -> string list -> class_expr -> lambda)

(* Probe handlers are generated from %probe as closed functions
   during transl_exp and immediately lifted to top level. *)
let probe_handlers = ref []
let clear_probe_handlers () = probe_handlers := []
let declare_probe_handlers lam =
  List.fold_left (fun acc (funcid, func) ->
      Llet(Strict, Pgenval, funcid, func, acc))
    lam
    !probe_handlers

(* Layout checking may default everything once we reach translcore *)
let is_void_sort s = Type_layout.Const.can_make_void (Layout.of_sort s)
let is_void_layout = Type_layout.Const.can_make_void

(* Compile an exception/extension definition *)

let prim_fresh_oo_id =
  Pccall (Primitive.simple ~name:"caml_fresh_oo_id" ~arity:1 ~alloc:false)

let transl_extension_constructor ~scopes env path ext =
  let path =
    Printtyp.wrap_printing_env env ~error:true (fun () ->
      Option.map (Printtyp.rewrite_double_underscore_longidents env) path)
  in
  let name =
    match path with
    | None -> Ident.name ext.ext_id
    | Some path -> Format.asprintf "%a" Pprintast.longident path
  in
  let loc = of_location ~scopes ext.ext_loc in
  match ext.ext_kind with
    Text_decl _ ->
      (* Extension constructors are currently always Alloc_heap.
         They could be Alloc_local, but that would require changes
         to pattern typing, as patterns can close over them. *)
      Lprim (Pmakeblock (Obj.object_tag, Immutable_unique, None, alloc_heap),
        [Lconst (Const_base (Const_string (name, ext.ext_loc, None)));
         Lprim (prim_fresh_oo_id, [Lconst (const_int 0)], loc)],
        loc)
  | Text_rebind(path, _lid) ->
      transl_extension_path loc env path

(* To propagate structured constants *)

exception Not_constant

let extract_constant = function
    Lconst sc -> sc
  | _ -> raise Not_constant

let extract_float = function
    Const_base(Const_float f) -> f
  | _ -> fatal_error "Translcore.extract_float"

let transl_alloc_mode alloc_mode =
  match Alloc_mode.constrain_lower alloc_mode with
  | Global -> alloc_heap
  | Local -> alloc_local

let transl_exp_mode e =
  let alloc_mode = Value_mode.regional_to_global_alloc e.exp_mode in
  transl_alloc_mode alloc_mode

let transl_apply_position position =
  match position with
  | Default -> Rc_normal
  | Nontail -> Rc_nontail
  | Tail ->
    if Config.stack_allocation then Rc_close_at_apply
    else Rc_normal

let may_allocate_in_region lam =
  let rec loop = function
    | Lvar _ | Lmutvar _ | Lconst _ -> ()

    | Lfunction {mode=Alloc_heap} -> ()
    | Lfunction {mode=Alloc_local} -> raise Exit

    | Lapply {ap_mode=Alloc_local}
    | Lsend (_,_,_,_,_,Alloc_local,_) -> raise Exit

    | Lprim (prim, args, _) ->
       begin match Lambda.primitive_may_allocate prim with
       | Some Alloc_local -> raise Exit
       | None | Some Alloc_heap ->
          List.iter loop args
       end
    | Lregion _body ->
       (* [_body] might do local allocations, but not in the current region *)
       ()
    | Lwhile {wh_cond_region=false} -> raise Exit
    | Lwhile {wh_body_region=false} -> raise Exit
    | Lwhile _ -> ()
    | Lfor {for_region=false} -> raise Exit
    | Lfor {for_from; for_to} -> loop for_from; loop for_to
    | ( Lapply _ | Llet _ | Lmutlet _ | Lletrec _ | Lswitch _ | Lstringswitch _
      | Lstaticraise _ | Lstaticcatch _ | Ltrywith _
      | Lifthenelse _ | Lsequence _ | Lassign _ | Lsend _
      | Levent _ | Lifused _) as lam ->
       Lambda.iter_head_constructor loop lam
  in
  if not Config.stack_allocation then false
  else begin
    match loop lam with
    | () -> false
    | exception Exit -> true
  end

let maybe_region lam =
  let rec remove_tail_markers = function
    | Lapply ({ap_region_close = Rc_close_at_apply} as ap) ->
       Lapply ({ap with ap_region_close = Rc_normal})
    | Lsend (k, lmet, lobj, largs, Rc_close_at_apply, mode, loc) ->
       Lsend (k, lmet, lobj, largs, Rc_normal, mode, loc)
    | Lregion _ as lam -> lam
    | lam ->
       Lambda.shallow_map ~tail:remove_tail_markers ~non_tail:Fun.id lam
  in
  if not Config.stack_allocation then lam
  else if may_allocate_in_region lam then Lregion lam
  else remove_tail_markers lam

(* Push the default values under the functional abstractions *)
(* Also push bindings of module patterns, since this sound *)

type binding =
  | Bind_value of value_binding list
  | Bind_module of Ident.t * string option loc * module_presence * module_expr

let wrap_bindings bindings exp =
  List.fold_left
    (fun exp binds ->
      {exp with exp_desc =
       match binds with
       | Bind_value binds -> Texp_let(Nonrecursive, binds, exp)
       | Bind_module (id, name, pres, mexpr) ->
           Texp_letmodule (Some id, name, pres, mexpr, exp)})
    exp bindings

let rec trivial_pat pat =
  match pat.pat_desc with
    Tpat_var _
  | Tpat_any -> true
  | Tpat_alias (p, _, _) ->
      trivial_pat p
  | Tpat_construct (_, cd, [], _) ->
      not cd.cstr_generalized && cd.cstr_consts = 1 && cd.cstr_nonconsts = 0
  | Tpat_tuple patl ->
      List.for_all trivial_pat patl
  | _ -> false

let rec push_defaults loc bindings use_lhs cases partial warnings =
  match cases with
    [{c_lhs=pat; c_guard=None;
      c_rhs={exp_desc = Texp_function { arg_label; param; cases; partial;
                                        region; curry; warnings } }
        as exp}] when bindings = [] || trivial_pat pat ->
      let cases = push_defaults exp.exp_loc bindings false cases partial warnings in
      [{c_lhs=pat; c_guard=None;
        c_rhs={exp with exp_desc = Texp_function { arg_label; param; cases;
          partial; region; curry; warnings }}}]
  | [{c_lhs=pat; c_guard=None;
      c_rhs={exp_attributes=[{Parsetree.attr_name = {txt="#default"};_}];
             exp_desc = Texp_let
               (Nonrecursive, binds,
                ({exp_desc = Texp_function _} as e2))}}] ->
      push_defaults loc (Bind_value binds :: bindings) true
                   [{c_lhs=pat;c_guard=None;c_rhs=e2}]
                   partial warnings
  | [{c_lhs=pat; c_guard=None;
      c_rhs={exp_attributes=[{Parsetree.attr_name = {txt="#modulepat"};_}];
             exp_desc = Texp_letmodule
               (Some id, name, pres, mexpr,
                ({exp_desc = Texp_function _} as e2))}}] ->
      push_defaults loc (Bind_module (id, name, pres, mexpr) :: bindings) true
                   [{c_lhs=pat;c_guard=None;c_rhs=e2}]
                   partial warnings
  | [{c_lhs=pat; c_guard=None; c_rhs=exp} as case]
    when use_lhs || trivial_pat pat && exp.exp_desc <> Texp_unreachable ->
      [{case with c_rhs = wrap_bindings bindings exp}]
  | {c_lhs=pat; c_rhs=exp; c_guard=_} :: _ when bindings <> [] ->
      let param = Typecore.name_cases "param" cases in
      let desc =
        {val_type = pat.pat_type; val_kind = Val_reg;
         val_attributes = []; Types.val_loc = Location.none;
         val_uid = Types.Uid.internal_not_actually_unique; }
      in
      let env = Env.add_value param desc exp.exp_env in
      let name = Ident.name param in
      let exp =
        let cases =
          let pure_case ({c_lhs; _} as case) =
            {case with c_lhs = as_computation_pattern c_lhs} in
          List.map pure_case cases in
        { exp with exp_loc = loc; exp_env = env; exp_desc =
          Texp_match
            ({exp with exp_type = pat.pat_type; exp_env = env; exp_desc =
              Texp_ident
                (Path.Pident param, mknoloc (Longident.Lident name),
                 desc, Id_value)},
             Types.Sort.value,
             (* CR ccasinghino Value here will changes when functions take other
                layouts *)
             cases, partial) }
      in
      [{c_lhs = {pat with pat_desc = Tpat_var (param, mknoloc name)};
        c_guard = None; c_rhs= wrap_bindings bindings exp}]
  | _ ->
      cases

let push_defaults loc = push_defaults loc [] false

(* Insertion of debugging events *)

let event_before ~scopes exp lam =
  Translprim.event_before (of_location ~scopes exp.exp_loc) exp lam

let event_after ~scopes exp lam =
  Translprim.event_after (of_location ~scopes exp.exp_loc) exp lam

let event_function ~scopes exp lam =
  if !Clflags.debug && not !Clflags.native_code then
    let repr = Some (ref 0) in
    let (info, body) = lam repr in
    (info,
     Levent(body, {lev_loc = of_location ~scopes exp.exp_loc;
                   lev_kind = Lev_function;
                   lev_repr = repr;
                   lev_env = exp.exp_env}))
  else
    lam None

(* Assertions *)

let assert_failed ~scopes exp =
  let slot =
    transl_extension_path Loc_unknown
      Env.initial_safe_string Predef.path_assert_failure
  in
  let loc = exp.exp_loc in
  let (fname, line, char) =
    Location.get_pos_info loc.Location.loc_start
  in
  let loc = of_location ~scopes exp.exp_loc in
  Lprim(Praise Raise_regular, [event_after ~scopes exp
    (Lprim(Pmakeblock(0, Immutable, None, alloc_heap),
          [slot;
           Lconst(Const_block(0,
              [Const_base(Const_string (fname, exp.exp_loc, None));
               Const_base(Const_int line);
               Const_base(Const_int char)]))], loc))], loc)
;;

let rec cut n l =
  if n = 0 then ([],l) else
  match l with [] -> failwith "Translcore.cut"
  | a::l -> let (l1,l2) = cut (n-1) l in (a::l1,l2)

(* Translation of expressions *)

let rec iter_exn_names f pat =
  match pat.pat_desc with
  | Tpat_var (id, _) -> f id
  | Tpat_alias (p, id, _) ->
      f id;
      iter_exn_names f p
  | _ -> ()

let transl_ident loc env ty path desc kind =
  match desc.val_kind, kind with
  | Val_prim p, Id_prim pmode ->
      let poly_mode = Option.map transl_alloc_mode pmode in
      Translprim.transl_primitive loc p env ty ~poly_mode (Some path)
  | Val_anc _, Id_value ->
      raise(Error(to_location loc, Free_super_var))
  | (Val_reg | Val_self _), Id_value ->
      transl_value_path loc env path
  |  _ -> fatal_error "Translcore.transl_exp: bad Texp_ident"

let can_apply_primitive p pmode pos args =
  let is_omitted = function
    | Arg _ -> false
    | Omitted _ -> true
  in
  if List.exists (fun (_, arg) -> is_omitted arg) args then false
  else begin
    let nargs = List.length args in
    if nargs = p.prim_arity then true
    else if nargs < p.prim_arity then false
    else if pos <> Typedtree.Tail then true
    else begin
      let return_mode = Ctype.prim_mode pmode p.prim_native_repr_res in
      is_heap_mode (transl_alloc_mode return_mode)
    end
  end

(* For a first pass, function arguments are not permitted types of kind void *)
let fun_arg_value_kind pat =
  value_kind pat.pat_env pat.pat_type

(* At the moment, we're translating "void" things to lambda with a little trick:
   We don't return a dummy value, like unit, from void expressions.  Instead,
   they jump to a continuation via Lstaticraise.  [transl_exp] checks whether
   the thing it's about to evaluate is a void and sets up a handler
   (Lstaticcatch) for this throw if so.

   Many translation functions take an argument (void_k : int option) argument.
   This represents a continuation to be used if the thing being translated is
   void.  The int is the name of a static exception handler that they will raise
   to in that case.  [void_k] must be [Some] iff the thing being translated is
   void.

   Annnoyingly, the lambda syntax has [value_kinds] in several places - mainly
   control flow join points - that are inconvenient for this trick.  E.g.,:

   | Lifthenelse of lambda * lambda * lambda * value_kind

   Here the value_kind is for the result of the ite.  That result can have a
   type whose layout is void, in which case there is no actual runtime value.
   In that case, each branch will Lstaticraise after running the relevant
   computation, so the value_kind is irrelevant - we never actually return a
   value.  We use [Pintval] in those cases.

   In the future, we'll add another type that tracks runtime layouts more fully,
   where [value_kind] just appears in the value case.  But that requires more
   reworks in the middle end, so we're using this Lstaticraise/Lstaticcatch
   trick for now. *)
let value_kind_if_not_void e void_k =
  match void_k with
  | None -> Typeopt.value_kind e.exp_env e.exp_type
  | Some _ -> Pintval

let catch_void body after kind =
  let static_exception_id = next_raise_count () in
  Lstaticcatch (body (Some static_exception_id),
                (static_exception_id, []),
                after,
                kind)

(* Translates lists of expressions, which must have at least one non-void
   element.  The resulting list has an element for each non-void element of the
   input.  Computations corresponding to the void elements are attached to the
   non-void elements in a way that preserves evaluation order.

   This is generalized to support using it on both lists of expressions and
   lists of record fields.  So it takes an ['a list] and some functions to
   do the various bits:

   is_void : 'a -> bool
   value_kind : 'a -> value_kind    (will only be called if not is_void)
   transl : 'a -> int option -> Lambda.t

*)
let transl_list_with_voids ~is_void ~value_kind ~transl expr_list =
  (* before and after are lists of void computations in reverse eval order.
     If before = after = [], this is the same as just translating e *)
  let transl_with_voids_before_and_after (before,e,after) =
    let transl_with_voids_after e after =
      let kind = value_kind e in
      match after with
      | [] -> (kind, transl None e)
      | _ ->
        let result_var = Ident.create_local "after_voids" in
        (kind,
         Llet (Strict, kind, result_var,
               transl None e,
               List.fold_left (fun lam e ->
                 catch_void (fun void_k -> transl void_k e) lam kind)
                 (Lvar result_var) after))
    in
    let transl_with_voids_before kind lam before =
      List.fold_left (fun lam e -> catch_void (fun void_k -> transl void_k e)
                                     lam kind)
        lam before
    in
    let (kind, lam) = transl_with_voids_after e after in
    (transl_with_voids_before kind lam before, kind)
  in
  let group_voids exprs =
    (* We need to group the voids with an element before them or the element
       after them.  We prefer to do them as part of an element after them in
       eval order, because doing them "before" an element is free while the
       alternative adds a let binding. *)
    let rec get_afters idx afters = function
      | e :: exprs when is_void e ->
        get_afters (idx + 1) (e :: afters) exprs
      | exprs -> (idx,exprs,afters)
    in
    let rec group idx befores nonvoid afters acc exprs =
      match exprs with
      | [] -> (List.rev befores,nonvoid, List.rev afters) :: acc
      | e :: exprs when is_void e ->
        group (idx+1) (e :: befores) nonvoid afters acc exprs
      | e :: exprs ->
        group (idx+1) [] e []
          ((List.rev befores,nonvoid,List.rev afters) :: acc) exprs
    in
    let (idx,exprs,afters) = get_afters 0 [] exprs in
    let (first_non_void,exprs) = match exprs with
      | [] -> assert false
      | (e :: exprs) -> e,exprs
    in
    List.rev (group (idx+1) [] first_non_void afters [] exprs)
  in
  let grouped = group_voids expr_list in
  List.split (List.map transl_with_voids_before_and_after grouped)

let rec transl_exp ~scopes void_k e =
  transl_exp1 ~scopes ~in_new_scope:false void_k e

(* ~in_new_scope tracks whether we just opened a new scope.

   We go to some trouble to avoid introducing many new anonymous function
   scopes, as `let f a b = ...` is desugared to several Pexp_fun.
*)
and transl_exp1 ~scopes ~in_new_scope void_k e =
  let eval_once =
    (* Whether classes for immediate objects must be cached *)
    match e.exp_desc with
      Texp_function _ | Texp_for _ | Texp_while _ -> false
    | _ -> true
  in
  if eval_once then transl_exp0 ~scopes ~in_new_scope void_k e else
  Translobj.oo_wrap e.exp_env true (transl_exp0 ~scopes ~in_new_scope void_k) e

(* [void_k] is [Some n] iff [e] has layout void, where [n] is a static handler
   address - see the comment on [value_kind_if_not_void]. *)
and transl_exp0 ~in_new_scope ~scopes void_k e =
  match e.exp_desc with
  | Texp_ident(path, _, desc, kind) -> begin
      match void_k with
      | None ->
        transl_ident (of_location ~scopes e.exp_loc)
          e.exp_env e.exp_type path desc kind
      | Some n -> Lstaticraise (n,[])
        (* CR ccasinghino: might we ever have, e.g., a void primitive for which
           we want to do something interesting here? *)
    end
  | Texp_constant cst ->
      Lconst(Const_base cst)
  | Texp_let(rec_flag, pat_expr_list, body) ->
      let body_kind = value_kind_if_not_void body void_k in
      transl_let ~scopes rec_flag pat_expr_list
        body_kind (event_before ~scopes body (transl_exp ~scopes void_k body))
  | Texp_function { arg_label = _; param; cases; partial;
                    region; curry; warnings } ->
      let scopes =
        if in_new_scope then scopes
        else enter_anonymous_function ~scopes
      in
      transl_function ~scopes e param cases partial warnings region curry
  | Texp_apply({ exp_desc = Texp_ident(path, _, {val_kind = Val_prim p},
                                       Id_prim pmode);
                exp_type = prim_type } as funct, oargs, pos)
    when can_apply_primitive p pmode pos oargs ->
      let argl, extra_args = cut p.prim_arity oargs in
      let arg_exps =
         List.map (function _, Arg x -> x | _ -> assert false) argl
      in
      let args = transl_list ~scopes arg_exps in
      let prim_exp = if extra_args = [] then Some e else None in
      let position =
        if extra_args = [] then transl_apply_position pos
        else Rc_normal
      in
      let prim_mode = Option.map transl_alloc_mode pmode in
      let lam =
        Translprim.transl_primitive_application
          (of_location ~scopes e.exp_loc) p e.exp_env prim_type prim_mode
          path prim_exp args arg_exps position
      in
      if extra_args = [] then lam
      else begin
        let tailcall = Translattribute.get_tailcall_attribute funct in
        let inlined = Translattribute.get_inlined_attribute funct in
        let specialised = Translattribute.get_specialised_attribute funct in
        let e = { e with exp_desc = Texp_apply(funct, oargs, pos) } in
        let position = transl_apply_position pos in
        let mode = transl_exp_mode e in
        event_after ~scopes e
          (transl_apply ~scopes ~tailcall ~inlined ~specialised ~position ~mode
             lam extra_args (of_location ~scopes e.exp_loc))
      end
  | Texp_apply(funct, oargs, position) ->
      let tailcall = Translattribute.get_tailcall_attribute funct in
      let inlined = Translattribute.get_inlined_attribute funct in
      let specialised = Translattribute.get_specialised_attribute funct in
      let e = { e with exp_desc = Texp_apply(funct, oargs, position) } in
      let position = transl_apply_position position in
      let mode = transl_exp_mode e in
      event_after ~scopes e
        (transl_apply ~scopes ~tailcall ~inlined ~specialised
           ~position ~mode (transl_exp ~scopes None funct)
           oargs (of_location ~scopes e.exp_loc))
  | Texp_match(arg, sort, pat_expr_list, partial) ->
      transl_match ~scopes e arg sort pat_expr_list partial void_k
  | Texp_try(body, pat_expr_list) ->
      let id = Typecore.name_cases "exn" pat_expr_list in
      let k = value_kind_if_not_void e void_k in
      Ltrywith(transl_exp ~scopes void_k body, id,
               Matching.for_trywith ~scopes k e.exp_loc (Lvar id)
                 (transl_cases_try ~scopes void_k pat_expr_list), k)
  | Texp_tuple el ->
      (* CR ccasinghino work to do here when we allow other layouts in tuples *)
      let ll = transl_list ~scopes el in
      let shape =
        List.map (fun e -> Typeopt.value_kind e.exp_env e.exp_type) el
      in
      begin try
        Lconst(Const_block(0, List.map extract_constant ll))
      with Not_constant ->
        Lprim(Pmakeblock(0, Immutable, Some shape,
                         transl_exp_mode e),
              ll,
              (of_location ~scopes e.exp_loc))
      end
  | Texp_construct(_, cstr, args) ->
      let transl_arg_list args =
        let args = List.mapi (fun i arg -> (i,arg)) args in
        let is_void (i,_) = is_void_layout cstr.cstr_arg_layouts.(i) in
        let value_kind (_,e) = Typeopt.value_kind e.exp_env e.exp_type in
        let transl void_k (_,e) = transl_exp ~scopes void_k e in
        transl_list_with_voids ~is_void ~value_kind ~transl args
      in
      if cstr.cstr_inlined <> None then begin match args with
        | [e] -> transl_exp ~scopes void_k e
        | _ -> assert false
      end else begin match cstr.cstr_tag, cstr.cstr_repr with
      | Ordinary {runtime_tag}, _ when cstr.cstr_constant ->
          (* In the constant case, any args must be void *)
          List.fold_left (fun l arg ->
            catch_void (fun void_k -> transl_exp ~scopes void_k arg)
              l Pintval)
          (Lconst(const_int runtime_tag)) args
      | Ordinary _, Variant_unboxed _ -> begin
          match args with
          | [arg] -> transl_exp ~scopes void_k arg
          | _ -> assert false
        end
      | Ordinary {runtime_tag}, Variant_boxed _ -> begin
          let ll, shape = transl_arg_list args in
          try
            (* CR ccasinghino: This optimization won't fire in the presence of
               voids (because of the way they get compiled with static
               exceptions).  But it wouldn't be too hard to fix - not doing it
               for now because we expect to revisit void compilation anyway.  *)
            Lconst(Const_block(runtime_tag, List.map extract_constant ll))
          with Not_constant ->
            Lprim(Pmakeblock(runtime_tag, Immutable, Some shape,
                             transl_exp_mode e),
                  ll,
                  of_location ~scopes e.exp_loc)
          end
      | Extension (path,_), Variant_extensible ->
          let lam = transl_extension_path
                      (of_location ~scopes e.exp_loc) e.exp_env path in
          if cstr.cstr_constant then lam
          else
            let ll, shape = transl_arg_list args in
            Lprim(Pmakeblock(0, Immutable, Some (Pgenval :: shape),
                             transl_exp_mode e),
                  lam :: ll, of_location ~scopes e.exp_loc)
      | Extension _, _ | _, Variant_extensible -> assert false
      end
  | Texp_extension_constructor (_, path) ->
      transl_extension_path (of_location ~scopes e.exp_loc) e.exp_env path
  | Texp_variant(l, arg) ->
      let tag = Btype.hash_variant l in
      begin match arg with
        None -> Lconst(const_int tag)
      | Some arg ->
          let lam = transl_exp ~scopes None arg in
          try
            Lconst(Const_block(0, [const_int tag;
                                   extract_constant lam]))
          with Not_constant ->
            Lprim(Pmakeblock(0, Immutable, None,
                             transl_exp_mode e),
                  [Lconst(const_int tag); lam],
                  of_location ~scopes e.exp_loc)
      end
  | Texp_record {fields; representation; extended_expression} ->
      let kind = value_kind_if_not_void e void_k in
      transl_record ~scopes void_k kind e.exp_loc e.exp_env
        (transl_exp_mode e)
        fields representation extended_expression
  | Texp_field(arg, _, lbl) -> begin
      match lbl.lbl_repres, void_k with
      | ((Record_unboxed l | Record_inlined (_, Variant_unboxed l)), Some n)
        when is_void_layout l ->
          (* Special case for projecting from records like
             type t = { t : some_void_type } [@@unboxed]
          *)
          catch_void (fun void_k -> transl_exp ~scopes void_k arg)
            (Lstaticraise (n,[])) Pintval
      | _ -> begin
        let targ = transl_exp ~scopes None arg in
        match void_k with
        | Some n -> Lsequence (targ, Lstaticraise (n, []))
        | None -> begin
          let sem =
            match lbl.lbl_mut with
            | Immutable -> Reads_agree
            | Mutable -> Reads_vary
          in
          match lbl.lbl_repres with
              Record_boxed _ | Record_inlined (_, Variant_boxed _) ->
              Lprim (Pfield (lbl.lbl_pos, sem), [targ],
                     of_location ~scopes e.exp_loc)
            | Record_unboxed _ | Record_inlined (_, Variant_unboxed _) -> targ
            | Record_float ->
              let mode = transl_exp_mode e in
              Lprim (Pfloatfield (lbl.lbl_pos, sem, mode), [targ],
                     of_location ~scopes e.exp_loc)
            | Record_inlined (_, Variant_extensible) ->
              Lprim (Pfield (lbl.lbl_pos + 1, sem), [targ],
                     of_location ~scopes e.exp_loc)
        end
      end
    end
  | Texp_setfield(arg, _, lbl, newval) -> begin
      if lbl.lbl_pos = lbl_pos_void then
        let transl_newval void_k = transl_exp ~scopes void_k newval in
        let arg = transl_exp ~scopes None arg in
        catch_void transl_newval (Lsequence (arg, lambda_unit)) Pintval
      else
        let mode =
          let arg_mode = Value_mode.regional_to_local_alloc arg.exp_mode in
          Assignment (transl_alloc_mode arg_mode)
        in
        let access =
          match lbl.lbl_repres with
            Record_boxed _
          | Record_inlined (_, Variant_boxed _) ->
            Psetfield(lbl.lbl_pos, maybe_pointer newval, mode)
          | Record_unboxed _ | Record_inlined (_, Variant_unboxed _) ->
            assert false
          | Record_float -> Psetfloatfield (lbl.lbl_pos, mode)
          | Record_inlined (_, Variant_extensible) ->
            Psetfield (lbl.lbl_pos + 1, maybe_pointer newval, mode)
        in
        Lprim(access,
              [transl_exp ~scopes None arg; transl_exp ~scopes None newval],
              of_location ~scopes e.exp_loc)
    end
  | Texp_array expr_list ->
      let kind = array_kind e in
      let ll = transl_list ~scopes expr_list in
      let mode = transl_exp_mode e in
      begin try
        (* For native code the decision as to which compilation strategy to
           use is made later.  This enables the Flambda passes to lift certain
           kinds of array definitions to symbols. *)
        (* Deactivate constant optimization if array is small enough *)
        if List.length ll <= use_dup_for_constant_arrays_bigger_than
        then begin
          raise Not_constant
        end;
        (* Pduparray only works in Alloc_heap mode *)
        if is_local_mode mode then raise Not_constant;
        begin match List.map extract_constant ll with
        | exception Not_constant when kind = Pfloatarray ->
            (* We cannot currently lift [Pintarray] arrays safely in Flambda
               because [caml_modify] might be called upon them (e.g. from
               code operating on polymorphic arrays, or functions such as
               [caml_array_blit].
               To avoid having different Lambda code for
               bytecode/Closure vs.  Flambda, we always generate
               [Pduparray] here, and deal with it in [Bytegen] (or in
               the case of Closure, in [Cmmgen], which already has to
               handle [Pduparray Pmakearray Pfloatarray] in the case
               where the array turned out to be inconstant).
               When not [Pfloatarray], the exception propagates to the handler
               below. *)
            let imm_array =
              Lprim (Pmakearray (kind, Immutable, mode), ll,
                     of_location ~scopes e.exp_loc)
            in
            Lprim (Pduparray (kind, Mutable), [imm_array],
                   of_location ~scopes e.exp_loc)
        | cl ->
            let imm_array =
              if Config.flambda2 then
                Lprim (Pmakearray (kind, Immutable, mode), ll,
                       of_location ~scopes e.exp_loc)
              else
                match kind with
                | Paddrarray | Pintarray ->
                  Lconst(Const_block(0, cl))
                | Pfloatarray ->
                  Lconst(Const_float_array(List.map extract_float cl))
                | Pgenarray ->
                  raise Not_constant    (* can this really happen? *)
            in
            Lprim (Pduparray (kind, Mutable), [imm_array],
                   of_location ~scopes e.exp_loc)
        end
      with Not_constant ->
        Lprim(Pmakearray (kind, Mutable, mode), ll,
              of_location ~scopes e.exp_loc)
      end
  | Texp_ifthenelse(cond, ifso, Some ifnot) ->
      let k = value_kind_if_not_void e void_k in
      Lifthenelse(transl_exp ~scopes None cond,
                  event_before ~scopes ifso (transl_exp ~scopes void_k ifso),
                  event_before ~scopes ifnot (transl_exp ~scopes void_k ifnot),
                  k)
  | Texp_ifthenelse(cond, ifso, None) ->
      Lifthenelse(transl_exp ~scopes None cond,
                  event_before ~scopes ifso (transl_exp ~scopes void_k ifso),
                  lambda_unit,
                  Pintval (* unit *))
  | Texp_sequence(expr1, layout, expr2) ->
      if is_void_layout layout then
        (* CR ccasinghino: Could we play a similar game for layout "any"? *)
        let kind2 = value_kind_if_not_void expr2 void_k in
        catch_void (fun void_k -> transl_exp ~scopes void_k expr1)
          (event_before ~scopes expr2
             (transl_exp ~scopes void_k expr2))
          kind2
      else
        Lsequence(transl_exp ~scopes None expr1,
                  event_before ~scopes expr2 (transl_exp ~scopes void_k expr2))
  | Texp_while {wh_cond; wh_cond_region;
                wh_body; wh_body_region; wh_body_layout} ->
      (* CR ccasinghino: Perhaps some cleverer encoding for void bodies is
         available, that doesn't use Lwhile and instead staticthrows right back
         to the condition. *)
      let cond = transl_exp ~scopes None wh_cond in
      let body =
        if is_void_layout wh_body_layout then
          catch_void (fun void_k -> transl_exp ~scopes void_k wh_body)
            lambda_unit Pintval
        else
          transl_exp ~scopes None wh_body
      in
      Lwhile {
        wh_cond = if wh_cond_region then maybe_region cond else cond;
        wh_cond_region;
        wh_body = event_before ~scopes wh_body
                    (if wh_body_region then maybe_region body else body);
        wh_body_region;
      }
  | Texp_arr_comprehension (body, blocks) ->
    (* CJC XXX (transl_exp None) below to be sorted out when we merge with the
       new comprehensions system *)
    (*One block consists of comprehension statements connected by "and".*)
    let loc = of_location ~scopes e.exp_loc in
    let array_kind = Typeopt.array_kind e in
    Translcomprehension.transl_arr_comprehension
      body blocks ~array_kind ~scopes ~loc ~transl_exp:(transl_exp None)
  | Texp_list_comprehension (body, blocks) ->
    (* CJC XXX (transl_exp None) below to be sorted out when we merge with the
       new comprehensions system *)
    let loc = of_location ~scopes e.exp_loc in
    Translcomprehension.transl_list_comprehension
      body blocks ~scopes ~loc ~transl_exp:(transl_exp None)
  | Texp_for {for_id; for_from; for_to; for_dir; for_body; for_body_layout;
              for_region} ->
      let body =
        if is_void_layout for_body_layout then
          catch_void (fun void_k -> transl_exp ~scopes void_k for_body)
            lambda_unit Pintval
        else
          transl_exp ~scopes None for_body
      in
      Lfor {
        for_id;
        for_from = transl_exp ~scopes None for_from;
        for_to = transl_exp ~scopes None for_to;
        for_dir;
        for_body = event_before ~scopes for_body
                     (if for_region then maybe_region body else body);
        for_region;
      }
  | Texp_send(expr, met, pos) ->
      let lam =
        let pos = transl_apply_position pos in
        let mode = transl_exp_mode e in
        let loc = of_location ~scopes e.exp_loc in
        match met with
        | Tmeth_val id ->
            let obj = transl_exp ~scopes None expr in
            Lsend (Self, Lvar id, obj, [], pos, mode, loc)
        | Tmeth_name nm ->
            let obj = transl_exp ~scopes None expr in
            let (tag, cache) = Translobj.meth obj nm in
            let kind = if cache = [] then Public else Cached in
            Lsend (kind, tag, obj, cache, pos, mode, loc)
        | Tmeth_ancestor(meth, path_self) ->
            let self = transl_value_path loc e.exp_env path_self in
            Lapply {ap_loc = loc;
                    ap_func = Lvar meth;
                    ap_args = [self];
                    ap_mode = mode;
                    ap_region_close = pos;
                    ap_probe = None;
                    ap_tailcall = Default_tailcall;
                    ap_inlined = Default_inlined;
                    ap_specialised = Default_specialise}
      in
      event_after ~scopes e lam
  | Texp_new (cl, {Location.loc=loc}, _, pos) ->
      let loc = of_location ~scopes loc in
      let pos = transl_apply_position pos in
      Lapply{
        ap_loc=loc;
        ap_func=
          Lprim(Pfield (0, Reads_vary),
              [transl_class_path loc e.exp_env cl], loc);
        ap_args=[lambda_unit];
        ap_region_close=pos;
        ap_mode=alloc_heap;
        ap_tailcall=Default_tailcall;
        ap_inlined=Default_inlined;
        ap_specialised=Default_specialise;
        ap_probe=None;
      }
  | Texp_instvar(path_self, path, _) ->
      let loc = of_location ~scopes e.exp_loc in
      let self = transl_value_path loc e.exp_env path_self in
      let var = transl_value_path loc e.exp_env path in
      Lprim(Pfield_computed Reads_vary, [self; var], loc)
  | Texp_setinstvar(path_self, path, _, expr) ->
      let loc = of_location ~scopes e.exp_loc in
      let self = transl_value_path loc e.exp_env path_self in
      let var = transl_value_path loc e.exp_env path in
      transl_setinstvar ~scopes loc self var expr
  | Texp_override(path_self, modifs) ->
      let loc = of_location ~scopes e.exp_loc in
      let self = transl_value_path loc e.exp_env path_self in
      let cpy = Ident.create_local "copy" in
      Llet(Strict, Pgenval, cpy,
           Lapply{
             ap_loc=Loc_unknown;
             ap_func=Translobj.oo_prim "copy";
             ap_args=[self];
             ap_region_close=Rc_normal;
             ap_mode=alloc_heap;
             ap_tailcall=Default_tailcall;
             ap_inlined=Default_inlined;
             ap_specialised=Default_specialise;
             ap_probe=None;
           },
           List.fold_right
             (fun (id, _, expr) rem ->
                Lsequence(transl_setinstvar ~scopes Loc_unknown
                            (Lvar cpy) (Lvar id) expr, rem))
             modifs
             (Lvar cpy))
  | Texp_letmodule(None, loc, Mp_present, modl, body) ->
      let lam = !transl_module ~scopes Tcoerce_none None modl in
      Lsequence(Lprim(Pignore, [lam], of_location ~scopes loc.loc),
                transl_exp ~scopes void_k body)
  | Texp_letmodule(Some id, loc, Mp_present, modl, body) ->
      let defining_expr =
        let mod_scopes = enter_module_definition ~scopes id in
        let lam = !transl_module ~scopes:mod_scopes Tcoerce_none None modl in
        Levent (lam, {
          lev_loc = of_location ~scopes loc.loc;
          lev_kind = Lev_module_definition id;
          lev_repr = None;
          lev_env = Env.empty;
        })
      in
      Llet(Strict, Pgenval, id, defining_expr, transl_exp ~scopes void_k body)
  | Texp_letmodule(_, _, Mp_absent, _, body) ->
      transl_exp ~scopes void_k body
  | Texp_letexception(cd, body) ->
      Llet(Strict, Pgenval,
           cd.ext_id, transl_extension_constructor ~scopes e.exp_env None cd,
           transl_exp ~scopes void_k body)
  | Texp_pack modl ->
      !transl_module ~scopes Tcoerce_none None modl
  | Texp_assert {exp_desc=Texp_construct(_, {cstr_name="false"}, _)} ->
      assert_failed ~scopes e
  | Texp_assert (cond) ->
      if !Clflags.noassert
      then lambda_unit
      else begin
        Lifthenelse
          (transl_exp ~scopes None cond,
           lambda_unit,
           assert_failed ~scopes e,
           Pintval (* unit *))
      end
  | Texp_lazy e ->
      (* when e needs no computation (constants, identifiers, ...), we
         optimize the translation just as Lazy.lazy_from_val would
         do *)
      assert (is_heap_mode (transl_exp_mode e));
      begin match Typeopt.classify_lazy_argument e with
      | `Constant_or_function ->
        (* A constant expr (of type <> float if [Config.flat_float_array] is
           true) gets compiled as itself. *)
         transl_exp ~scopes None e
      | `Float_that_cannot_be_shortcut ->
          (* We don't need to wrap with Popaque: this forward
             block will never be shortcutted since it points to a float
             and Config.flat_float_array is true. *)
         Lprim(Pmakeblock(Obj.forward_tag, Immutable, None,
                          alloc_heap),
                [transl_exp ~scopes None e], of_location ~scopes e.exp_loc)
      | `Identifier `Forward_value ->
         (* CR-someday mshinwell: Consider adding a new primitive
            that expresses the construction of forward_tag blocks.
            We need to use [Popaque] here to prevent unsound
            optimisation in Flambda, but the concept of a mutable
            block doesn't really match what is going on here.  This
            value may subsequently turn into an immediate... *)
         Lprim (Popaque,
                [Lprim(Pmakeblock(Obj.forward_tag, Immutable, None,
                                  alloc_heap),
                       [transl_exp ~scopes None e],
                       of_location ~scopes e.exp_loc)],
                of_location ~scopes e.exp_loc)
      | `Identifier `Other ->
         transl_exp ~scopes None e
      | `Other ->
         (* other cases compile to a lazy block holding a function *)
         let scopes = enter_lazy ~scopes in
         let fn = lfunction ~kind:(Curried {nlocal=0})
                            ~params:[Ident.create_local "param", Pgenval]
                            ~return:Pgenval
                            ~attr:default_function_attribute
                            ~loc:(of_location ~scopes e.exp_loc)
                            ~mode:alloc_heap
                            ~region:true
                            ~body:(maybe_region (transl_exp ~scopes None e))
         in
          Lprim(Pmakeblock(Config.lazy_tag, Mutable, None, alloc_heap), [fn],
                of_location ~scopes e.exp_loc)
      end
  | Texp_object (cs, meths) ->
      let cty = cs.cstr_type in
      let cl = Ident.create_local "object" in
      !transl_object ~scopes cl meths
        { cl_desc = Tcl_structure cs;
          cl_loc = e.exp_loc;
          cl_type = Cty_signature cty;
          cl_env = e.exp_env;
          cl_attributes = [];
         }
  | Texp_letop{let_; ands; param; body; partial; warnings} ->
      event_after ~scopes e
        (transl_letop ~scopes e.exp_loc e.exp_env let_ ands
           param body partial warnings)
  | Texp_unreachable ->
      raise (Error (e.exp_loc, Unreachable_reached))
  | Texp_open (od, e) ->
      let pure = pure_module od.open_expr in
      (* this optimization shouldn't be needed because Simplif would
          actually remove the [Llet] when it's not used.
          But since [scan_used_globals] runs before Simplif, we need to
          do it. *)
      begin match od.open_bound_items with
      | [] when pure = Alias -> transl_exp ~scopes void_k e
      | _ ->
          let oid = Ident.create_local "open" in
          let body, _ =
            (* CR ccasinghino Currently only allow values at the top level.
               When we allow other layouts, and particularly void, we'll need
               adjustments here. *)
            List.fold_left (fun (body, pos) id ->
              Llet(Alias, Pgenval, id,
                   Lprim(mod_field pos, [Lvar oid],
                         of_location ~scopes od.open_loc), body),
              pos + 1
            ) (transl_exp ~scopes void_k e, 0)
              (bound_value_identifiers od.open_bound_items)
          in
          Llet(pure, Pgenval, oid,
               !transl_module ~scopes Tcoerce_none None od.open_expr, body)
      end
  | Texp_probe {name; handler=exp} ->
    if !Clflags.native_code && !Clflags.probes then begin
      let lam = transl_exp ~scopes None exp in
      let map =
        Ident.Set.fold (fun v acc -> Ident.Map.add v (Ident.rename v) acc)
          (free_variables lam)
          Ident.Map.empty
      in
      let arg_idents, param_idents = Ident.Map.bindings map |> List.split in
      let body = Lambda.rename map lam in
      let attr =
        { inline = Never_inline;
          specialise = Always_specialise;
          local = Never_local;
          check = Default_check;
          loop = Never_loop;
          is_a_functor = false;
          stub = false;
          poll = Default_poll;
          tmc_candidate = false;
        } in
      let funcid = Ident.create_local ("probe_handler_" ^ name) in
      let handler =
        let scopes = enter_value_definition ~scopes funcid in
        lfunction
          ~kind:(Curried {nlocal=0})
          ~params:(List.map (fun v -> v, Pgenval) param_idents)
          ~return:Pgenval
          ~body
          ~loc:(of_location ~scopes exp.exp_loc)
          ~attr
          ~mode:alloc_heap
          ~region:true
      in
      let app =
        { ap_func = Lvar funcid;
          ap_args = List.map (fun id -> Lvar id) arg_idents;
          ap_region_close = Rc_normal;
          ap_mode = alloc_heap;
          ap_loc = of_location e.exp_loc ~scopes;
          ap_tailcall = Default_tailcall;
          ap_inlined = Never_inlined;
          ap_specialised = Always_specialise;
          ap_probe = Some {name};
        }
      in
      begin match Config.flambda || Config.flambda2 with
      | true ->
          Llet(Strict, Pgenval, funcid, handler, Lapply app)
      | false ->
        (* Needs to be lifted to top level manually here,
           because functions that contain other function declarations
           are not inlined by Closure. For example, adding a probe into
           the body of function foo will prevent foo from being inlined
           into another function. *)
        probe_handlers := (funcid, handler)::!probe_handlers;
        Lapply app
      end
    end else begin
      lambda_unit
    end
  | Texp_probe_is_enabled {name} ->
    if !Clflags.native_code && !Clflags.probes then
      Lprim(Pprobe_is_enabled {name}, [], of_location ~scopes e.exp_loc)
    else
      lambda_unit

and pure_module m =
  match m.mod_desc with
    Tmod_ident _ -> Alias
  | Tmod_constraint (m,_,_,_) -> pure_module m
  | _ -> Strict

(* list elements must be non-void *)
and transl_list ~scopes expr_list =
  List.map (transl_exp ~scopes None) expr_list

and transl_guard ~scopes void_k guard rhs =
  let kind = value_kind_if_not_void rhs void_k in
  let expr = event_before ~scopes rhs (transl_exp ~scopes void_k rhs) in
  match guard with
  | None -> expr
  | Some cond ->
      event_before ~scopes cond
        (Lifthenelse(transl_exp ~scopes None cond, expr, staticfail, kind))

and transl_case ~scopes void_k {c_lhs; c_guard; c_rhs} =
  c_lhs, transl_guard ~scopes void_k c_guard c_rhs

and transl_cases ~scopes void_k cases =
  let cases =
    List.filter (fun c -> c.c_rhs.exp_desc <> Texp_unreachable) cases in
  List.map (transl_case ~scopes void_k) cases

and transl_case_try ~scopes void_k {c_lhs; c_guard; c_rhs} =
  iter_exn_names Translprim.add_exception_ident c_lhs;
  Misc.try_finally
    (fun () -> c_lhs, transl_guard ~scopes void_k c_guard c_rhs)
    ~always:(fun () ->
        iter_exn_names Translprim.remove_exception_ident c_lhs)

and transl_cases_try ~scopes void_k cases =
  let cases =
    List.filter (fun c -> c.c_rhs.exp_desc <> Texp_unreachable) cases in
  List.map (transl_case_try ~scopes void_k) cases

and transl_tupled_cases ~scopes patl_expr_list =
  let patl_expr_list =
    List.filter (fun (_,_,e) -> e.exp_desc <> Texp_unreachable)
      patl_expr_list in
  (* Because this is used only for function bodies, we can assume there is no
     void continuation (the None to transl_guard).  Will change when function
     may return void. *)
  List.map (fun (patl, guard, expr) ->
    (patl, transl_guard ~scopes None guard expr))
    patl_expr_list

and transl_apply ~scopes
      ?(tailcall=Default_tailcall)
      ?(inlined = Default_inlined)
      ?(specialised = Default_specialise)
      ?(position=Rc_normal)
      ?(mode=alloc_heap)
      lam sargs loc
  =
  let lapply funct args loc pos mode =
    match funct, pos with
    | Lsend((Self | Public) as k, lmet, lobj, [], _, _, _), _ ->
        Lsend(k, lmet, lobj, args, pos, mode, loc)
    | Lsend(Cached, lmet, lobj, ([_; _] as largs), _, _, _), _ ->
        Lsend(Cached, lmet, lobj, largs @ args, pos, mode, loc)
    | Lsend(k, lmet, lobj, largs, (Rc_normal | Rc_nontail), _, _),
      (Rc_normal | Rc_nontail) ->
        Lsend(k, lmet, lobj, largs @ args, pos, mode, loc)
    | Levent(
      Lsend((Self | Public) as k, lmet, lobj, [], _, _, _), _), _ ->
        Lsend(k, lmet, lobj, args, pos, mode, loc)
    | Levent(
      Lsend(Cached, lmet, lobj, ([_; _] as largs), _, _, _), _), _ ->
        Lsend(Cached, lmet, lobj, largs @ args, pos, mode, loc)
    | Levent(
      Lsend(k, lmet, lobj, largs, (Rc_normal | Rc_nontail), _, _), _),
      (Rc_normal | Rc_nontail) ->
        Lsend(k, lmet, lobj, largs @ args, pos, mode, loc)
    | Lapply ({ ap_region_close = (Rc_normal | Rc_nontail) } as ap),
      (Rc_normal | Rc_nontail) ->
        Lapply
          {ap with ap_args = ap.ap_args @ args; ap_loc = loc;
                   ap_region_close = pos; ap_mode = mode}
    | lexp, _ ->
        Lapply {
          ap_loc=loc;
          ap_func=lexp;
          ap_args=args;
          ap_region_close=pos;
          ap_mode=mode;
          ap_tailcall=tailcall;
          ap_inlined=inlined;
          ap_specialised=specialised;
          ap_probe=None;
        }
  in
  let rec build_apply lam args loc pos ap_mode = function
    | Omitted { mode_closure; mode_arg; mode_ret } :: l ->
        assert (pos = Rc_normal);
        let defs = ref [] in
        let protect name lam =
          match lam with
            Lvar _ | Lconst _ -> lam
          | _ ->
              let id = Ident.create_local name in
              defs := (id, lam) :: !defs;
              Lvar id
        in
        let lam =
          if args = [] then lam else lapply lam (List.rev args) loc pos ap_mode
        in
        let handle = protect "func" lam in
        let l =
          List.map
            (fun arg ->
               match arg with
               | Omitted _ -> arg
               | Arg arg -> Arg (protect "arg" arg))
            l
        in
        let id_arg = Ident.create_local "param" in
        let body =
          let loc = map_scopes enter_partial_or_eta_wrapper loc in
          let mode = transl_alloc_mode mode_closure in
          let arg_mode = transl_alloc_mode mode_arg in
          let ret_mode = transl_alloc_mode mode_ret in
          let body = build_apply handle [Lvar id_arg] loc Rc_normal ret_mode l in
          let nlocal =
            match join_mode mode (join_mode arg_mode ret_mode) with
            | Alloc_local -> 1
            | Alloc_heap -> 0
          in
          let region =
            match ret_mode with
            | Alloc_local -> false
            | Alloc_heap -> true
          in
          lfunction ~kind:(Curried {nlocal}) ~params:[id_arg, Pgenval]
                    ~return:Pgenval ~body ~mode ~region
                    ~attr:default_stub_attribute ~loc
        in
        List.fold_right
          (fun (id, lam) body -> Llet(Strict, Pgenval, id, lam, body))
          !defs body
    | Arg arg :: l -> build_apply lam (arg :: args) loc pos ap_mode l
    | [] -> lapply lam (List.rev args) loc pos ap_mode
  in
  let args =
    List.map
      (fun (_, arg) ->
         match arg with
         | Omitted _ as arg -> arg
         | Arg exp -> Arg (transl_exp ~scopes None exp))
      sargs
  in
  build_apply lam [] loc position mode args

and transl_curried_function
      ~scopes loc return
      repr ~region ~curry partial warnings (param:Ident.t) cases =
  let max_arity = Lambda.max_arity () in
  let rec loop ~scopes loc return ~arity ~region ~curry
            partial warnings (param:Ident.t) cases =
    match curry, cases with
      More_args {partial_mode},
      [{c_lhs=pat; c_guard=None;
        c_rhs={exp_desc =
                 Texp_function
                   { arg_label = _; param = param'; cases = cases';
                     partial = partial'; region = region';
                     curry = curry';
                     warnings = warnings' };
               exp_env; exp_type; exp_loc }}]
      when arity < max_arity ->
      (* Lfunctions must have local returns after the first local arg/ret *)
      if Parmatch.inactive ~partial pat
      then
        let partial_mode = transl_alloc_mode partial_mode in
        let kind = fun_arg_value_kind pat in
        let return_kind = function_return_value_kind exp_env exp_type in
        let ((fnkind, params, return, region), body) =
          loop ~scopes exp_loc return_kind
            ~arity:(arity + 1) ~region:region' ~curry:curry'
            partial' warnings' param' cases'
        in
        let fnkind =
          match partial_mode, fnkind with
          | _, Tupled ->
             (* arity > 1 prevents this *)
             assert false
          | Alloc_heap, (Curried _ as c) -> c
          | Alloc_local, Curried {nlocal} ->
             (* all subsequent curried arrows should be local *)
             assert (nlocal = List.length params);
             Curried {nlocal = nlocal + 1}
        in
        ((fnkind, (param, kind) :: params, return, region),
         Matching.for_function ~scopes return_kind loc None (Lvar param)
           [pat, body] partial)
      else begin
        begin match partial with
        | Total ->
            let prev = Warnings.backup () in
            Warnings.restore warnings;
            Location.prerr_warning pat.pat_loc
              Match_on_mutable_state_prevent_uncurry;
            Warnings.restore prev
        | Partial -> ()
        end;
        transl_tupled_function ~scopes ~arity ~region ~curry
          loc return repr partial param cases
      end
    | curry, cases ->
      transl_tupled_function ~scopes ~arity ~region ~curry
        loc return repr partial param cases
  in
  loop ~scopes loc return ~arity:1 ~region ~curry
    partial warnings param cases

and transl_tupled_function
      ~scopes ~arity ~region ~curry loc return
      repr partial (param:Ident.t) cases =
  let partial_mode =
    match curry with
    | More_args {partial_mode} | Final_arg {partial_mode} ->
      transl_alloc_mode partial_mode
  in
  match partial_mode, cases with
  | Alloc_heap, {c_lhs={pat_desc = Tpat_tuple pl }} :: _
    when !Clflags.native_code
      && arity = 1
      && List.length pl <= (Lambda.max_arity ()) ->
      begin try
        let size = List.length pl in
        let pats_expr_list =
          List.map
            (fun {c_lhs; c_guard; c_rhs} ->
              (Matching.flatten_pattern size c_lhs, c_guard, c_rhs))
            cases in
        let kinds =
          (* All the patterns might not share the same types. We must take the
             union of the patterns types *)
          match pats_expr_list with
          | [] -> assert false
          | (pats, _, _) :: cases ->
              let first_case_kinds = List.map fun_arg_value_kind pats in
              List.fold_left
                (fun kinds (pats, _, _) ->
                   List.map2 (fun kind pat ->
                       value_kind_union kind (fun_arg_value_kind pat))
                     kinds pats)
                first_case_kinds cases
        in
        let tparams =
          List.map (fun kind -> Ident.create_local "param", kind) kinds
        in
        let params = List.map fst tparams in
        let body =
          Matching.for_tupled_function ~scopes loc return params
            (transl_tupled_cases ~scopes pats_expr_list) partial
        in
        let region = region || not (may_allocate_in_region body) in
        ((Tupled, tparams, return, region), body)
    with Matching.Cannot_flatten ->
      transl_function0 ~scopes loc ~region ~partial_mode
        return repr partial param cases
      end
  | _ -> transl_function0 ~scopes loc ~region ~partial_mode
           return repr partial param cases

and transl_function0
      ~scopes loc ~region ~partial_mode return
      repr partial (param:Ident.t) cases =
    let kind =
      match cases with
      | [] ->
        (* With Camlp4, a pattern matching might be empty *)
        Pgenval
      | {c_lhs=pat} :: other_cases ->
        (* All the patterns might not share the same types. We must take the
           union of the patterns types *)
        List.fold_left (fun k {c_lhs=pat} ->
          Typeopt.value_kind_union k (fun_arg_value_kind pat))
          (fun_arg_value_kind pat) other_cases
    in
    let body =
      Matching.for_function ~scopes return loc repr (Lvar param)
        (transl_cases ~scopes None cases) partial
    in
    let region = region || not (may_allocate_in_region body) in
    let nlocal =
      if not region then 1
      else match partial_mode with
        | Alloc_local -> 1
        | Alloc_heap -> 0
    in
    ((Curried {nlocal}, [param, kind], return, region), body)

and transl_function ~scopes e param cases partial warnings region curry =
  let mode = transl_exp_mode e in
  let ((kind, params, return, region), body) =
    event_function ~scopes e
      (function repr ->
         let pl = push_defaults e.exp_loc cases partial warnings in
         let return_kind = function_return_value_kind e.exp_env e.exp_type in
         transl_curried_function ~scopes e.exp_loc return_kind
           repr ~region ~curry partial warnings param pl)
  in
  let attr = default_function_attribute in
  let loc = of_location ~scopes e.exp_loc in
  let body = if region then maybe_region body else body in
  let lam = lfunction ~kind ~params ~return ~body ~attr ~loc ~mode ~region in
  Translattribute.add_function_attributes lam e.exp_loc e.exp_attributes

(* Like transl_exp, but used when a new scope was just introduced. *)
and transl_scoped_exp ~scopes void_k expr =
  transl_exp1 ~scopes ~in_new_scope:true void_k expr

(* Decides whether a pattern binding should introduce a new scope. *)
and transl_bound_exp ~scopes ~in_structure void_k pat expr =
  let should_introduce_scope =
    match expr.exp_desc with
    | Texp_function _ -> true
    | _ when in_structure -> true
    | _ -> false in
  match pat_bound_idents pat with
  | (id :: _) when should_introduce_scope ->
     transl_scoped_exp ~scopes:(enter_value_definition ~scopes id) void_k expr
  | _ -> transl_exp ~scopes void_k expr

(*
  Notice: transl_let consumes (ie compiles) its pat_expr_list argument,
  and returns a function that will take the body of the lambda-let construct.
  This complication allows choosing any compilation order for the
  bindings and body of let constructs.
*)
and transl_let ~scopes ?(add_regions=false) ?(in_structure=false)
               rec_flag pat_expr_list body_kind =
  match rec_flag with
    Nonrecursive ->
      let rec transl = function
        [] ->
          fun body -> body
      | {vb_pat=pat; vb_expr=expr; vb_sort=sort; vb_attributes=attr; vb_loc}
        :: rem ->
          let param_void_k =
            if is_void_sort sort then Some (next_raise_count ())
            else None
          in
          let lam =
            transl_bound_exp ~scopes ~in_structure param_void_k pat expr
          in
          let lam = Translattribute.add_function_attributes lam vb_loc attr in
          let lam = if add_regions then maybe_region lam else lam in
          let mk_body = transl rem in
          fun body ->
            Matching.for_let ~scopes pat.pat_loc param_void_k lam sort pat
              body_kind (mk_body body)
      in
      transl pat_expr_list
  | Recursive ->
      let idlist =
        List.map
          (fun {vb_pat=pat} -> match pat.pat_desc with
              Tpat_var (id,_) -> id
            | _ -> assert false)
        pat_expr_list in
      let transl_case {vb_expr=expr; vb_sort; vb_attributes; vb_loc; vb_pat}
            id =
        let bound_void_k =
          if is_void_sort vb_sort then Some (next_raise_count ()) else None
        in
        let lam =
          transl_bound_exp ~scopes ~in_structure bound_void_k vb_pat expr
        in
        let lam =
          Translattribute.add_function_attributes lam vb_loc vb_attributes
        in
        let lam = if add_regions then maybe_region lam else lam in
        begin match transl_exp_mode expr, lam with
        | Alloc_heap, _ -> ()
        | Alloc_local, Lfunction _ -> ()
        | _ -> Misc.fatal_error "transl_let: local recursive non-function"
        end;
        (id, lam) in
      let lam_bds = List.map2 transl_case pat_expr_list idlist in
      fun body -> Lletrec(lam_bds, body)

and transl_setinstvar ~scopes loc self var expr =
  Lprim(Psetfield_computed (maybe_pointer expr, Assignment alloc_heap),
    [self; var; transl_exp ~scopes None expr], loc)

and transl_record ~scopes void_k kind loc env mode fields repres opt_init_expr =
  let size = Array.length fields in
  (* Determine if there are "enough" fields (only relevant if this is a
     functional-style record update *)
  let no_init = match opt_init_expr with None -> true | _ -> false in
  match repres with
  | (Record_unboxed l | Record_inlined (_, Variant_unboxed l))
    when is_void_layout l -> begin
    let field =
      match fields.(0) with
      | (_, Kept _) -> assert false
      | (_, Overridden (_, e)) -> transl_exp ~scopes void_k e
    in
    match opt_init_expr with
    | None -> field
    | Some e ->
      catch_void (fun void_k -> transl_exp ~scopes void_k e) field Pintval
    end
  | _ when no_init || size < Config.max_young_wosize || is_local_mode mode ->
    begin
    (* Allocate new record with given fields (and remaining fields
       taken from init_expr if any *)
    let init_id = Ident.create_local "init" in
    let ll, shape =
      let is_void (lbl, _) = lbl.lbl_pos = lbl_pos_void in
      let value_kind (_, def) =
        match def with
        | Kept typ -> Typeopt.value_kind env typ
        | Overridden (_, expr) -> Typeopt.value_kind expr.exp_env expr.exp_type
      in
      let transl void_k (lbl, definition) =
        match definition, void_k with
        | Overridden (_, expr), _ -> transl_exp ~scopes void_k expr
        | Kept _, Some n -> Lstaticraise (n, [])
          (* CR ccasinghino - we could put an optimization in
             [transl_list_with_voids] that omits the Lstaticraise and catch in
             this case. *)
        | Kept _, None ->
          let sem =
            match lbl.lbl_mut with
            | Immutable -> Reads_agree
            | Mutable -> Reads_vary
          in
          let access =
            match repres with
            | Record_boxed _ | Record_inlined (_, Variant_boxed _) ->
              Pfield (lbl.lbl_pos, sem)
            | Record_unboxed _ | Record_inlined (_, Variant_unboxed _) ->
              assert false
            | Record_inlined (_, Variant_extensible) ->
              Pfield (lbl.lbl_pos + 1, sem)
            | Record_float ->
              (* This allocation is always deleted,
                 so it's simpler to leave it Alloc_heap *)
              Pfloatfield (lbl.lbl_pos, sem, alloc_heap)
          in
          Lprim(access, [Lvar init_id], of_location ~scopes loc)
      in
      (* Safe because we disallow records with only voids *)
      transl_list_with_voids ~is_void ~value_kind ~transl (Array.to_list fields)
    in
    let mut : Lambda.mutable_flag =
      if Array.exists (fun (lbl, _) -> lbl.lbl_mut = Asttypes.Mutable) fields
      then Mutable
      else Immutable in
    let lam =
      try
        if mut = Mutable then raise Not_constant;
        let cl = List.map extract_constant ll in
        match repres with
        | Record_boxed _ -> Lconst(Const_block(0, cl))
        | Record_inlined (Ordinary {runtime_tag}, Variant_boxed _) ->
            Lconst(Const_block(runtime_tag, cl))
        | Record_unboxed _ | Record_inlined (_, Variant_unboxed _) ->
            Lconst(match cl with [v] -> v | _ -> assert false)
        | Record_float ->
            Lconst(Const_float_block(List.map extract_float cl))
        | Record_inlined (_, Variant_extensible)
        | Record_inlined (Extension _, _) ->
            raise Not_constant
      with Not_constant ->
        let loc = of_location ~scopes loc in
        match repres with
          Record_boxed _ ->
            Lprim(Pmakeblock(0, mut, Some shape, mode), ll, loc)
        | Record_inlined (Ordinary {runtime_tag}, Variant_boxed _) ->
            Lprim(Pmakeblock(runtime_tag, mut, Some shape, mode), ll, loc)
        | Record_unboxed _ | Record_inlined (Ordinary _, Variant_unboxed _) ->
            (match ll with [v] -> v | _ -> assert false)
        | Record_float ->
            Lprim(Pmakefloatblock (mut, mode), ll, loc)
        | Record_inlined (Extension (path,_), Variant_extensible) ->
            let slot = transl_extension_path loc env path in
            Lprim(Pmakeblock(0, mut, Some (Pgenval :: shape), mode),
                  slot :: ll, loc)
        | Record_inlined (Extension _, (Variant_unboxed _ | Variant_boxed _))
        | Record_inlined (Ordinary _, Variant_extensible) ->
            assert false
    in
    begin match opt_init_expr with
      None -> lam
    | Some init_expr -> Llet(Strict, Pgenval, init_id,
                             transl_exp ~scopes None init_expr, lam)
    end
    end
  | _ -> begin
    (* Take a shallow copy of the init record, then mutate the fields
       of the copy *)
    let copy_id = Ident.create_local "newrecord" in
    let update_field cont = function
      | (_, Kept _) -> cont
      | (lbl, Overridden (_, expr)) when lbl.lbl_pos = lbl_pos_void ->
        catch_void (fun void_k -> transl_exp ~scopes void_k expr)
          cont kind
      | (lbl, Overridden (_, expr)) ->
          let upd =
            match repres with
              Record_boxed _ | Record_inlined (_, Variant_boxed _) ->
                let ptr = maybe_pointer expr in
                Psetfield(lbl.lbl_pos, ptr, Assignment alloc_heap)
            | Record_unboxed _ | Record_inlined (_, Variant_unboxed _) ->
                assert false
            | Record_float ->
                Psetfloatfield (lbl.lbl_pos, Assignment alloc_heap)
            | Record_inlined (_, Variant_extensible) ->
                let pos = lbl.lbl_pos + 1 in
                let ptr = maybe_pointer expr in
                Psetfield(pos, ptr, Assignment alloc_heap)
          in
          Lsequence(Lprim(upd, [Lvar copy_id; transl_exp ~scopes None expr],
                          of_location ~scopes loc),
                    cont)
    in
    begin match opt_init_expr with
      None -> assert false
    | Some init_expr ->
        assert (is_heap_mode mode); (* Pduprecord must be Alloc_heap *)
        Llet(Strict, Pgenval, copy_id,
             Lprim(Pduprecord (repres, size), [transl_exp ~scopes None init_expr],
                   of_location ~scopes loc),
             Array.fold_left update_field (Lvar copy_id) fields)
    end
  end

and transl_match ~scopes e arg sort pat_expr_list partial void_k =
  let kind = value_kind_if_not_void e void_k in
  let rewrite_case (val_cases, exn_cases, static_handlers as acc)
        ({ c_lhs; c_guard; c_rhs } as case) =
    if c_rhs.exp_desc = Texp_unreachable then acc else
    let val_pat, exn_pat = split_pattern c_lhs in
    match val_pat, exn_pat with
    | None, None -> assert false
    | Some pv, None ->
        let val_case =
          transl_case ~scopes void_k { case with c_lhs = pv }
        in
        val_case :: val_cases, exn_cases, static_handlers
    | None, Some pe ->
        let exn_case =
          transl_case_try ~scopes void_k { case with c_lhs = pe }
        in
        val_cases, exn_case :: exn_cases, static_handlers
    | Some pv, Some pe ->
        assert (c_guard = None);
        let lbl  = next_raise_count () in
        let static_raise ids =
          Lstaticraise (lbl, List.map (fun id -> Lvar id) ids)
        in
        (* Simplif doesn't like it if binders are not uniq, so we make sure to
           use different names in the value and the exception branches. *)
        let ids_full = Typedtree.pat_bound_idents_full sort pv in
        let ids_kinds =
          List.filter_map (fun (id, _, ty, sort) ->
            if Type_layout.Const.can_make_void (Layout.of_sort sort)
            then None
            else Some (id, Typeopt.value_kind pv.pat_env ty))
            ids_full
        in
        let ids = List.map (fun (id, _) -> id) ids_kinds in
        let vids = List.map Ident.rename ids in
        (* Note that alpha_pat turns the removed void vars to Tpat_any, which is
           fine because their uses are compiled away. *)
        let pv = alpha_pat (List.combine ids vids) pv in
        (* Also register the names of the exception so Re-raise happens. *)
        iter_exn_names Translprim.add_exception_ident pe;
        let rhs =
          Misc.try_finally
            (fun () -> event_before ~scopes c_rhs
                         (transl_exp ~scopes void_k c_rhs))
            ~always:(fun () ->
                iter_exn_names Translprim.remove_exception_ident pe)
        in
        (pv, static_raise vids) :: val_cases,
        (pe, static_raise ids) :: exn_cases,
        (lbl, ids_kinds, rhs) :: static_handlers
  in
  let val_cases, exn_cases, static_handlers =
    let x, y, z = List.fold_left rewrite_case ([], [], []) pat_expr_list in
    List.rev x, List.rev y, List.rev z
  in
  let lam_match =
    if is_void_sort sort then
      (* CR ccasinghino: The use of [Matching.for_function] here feels a bit
         sneaky, and results in an unneeded let binding even after simplif.  I'm
         not going to fix this now, or attempt to fold this code into the
         non-void cases below, because a) we plan to revise how void is
         compiled.  But if we keep this, some re-thinking is in order, and b)
         this structure makes it easier to see that the behavior is unchanged in
         the non-void case (reviewers: note that the original code for the
         non-void has been nested under an if, but is essentially unchanged) *)
      match exn_cases with
      | [] ->
        catch_void (fun void_k -> transl_exp ~scopes void_k arg)
          (Matching.for_function ~scopes kind e.exp_loc
             None lambda_unit val_cases partial)
          kind
      | _ :: _ ->
        let id = Typecore.name_pattern "exn" (List.map fst exn_cases) in
        let transl_arg void_k =
          Ltrywith(
            transl_exp ~scopes void_k arg, id,
            Matching.for_trywith ~scopes kind e.exp_loc (Lvar id) exn_cases,
            kind)
        in
        catch_void
          transl_arg
          (Matching.for_function ~scopes kind e.exp_loc
             None lambda_unit val_cases partial)
          kind
    else
      (* In presence of exception patterns, the code we generate for

           match <scrutinees> with
           | <val-patterns> -> <val-actions>
           | <exn-patterns> -> <exn-actions>

         looks like

           staticcatch
             (try (exit <val-exit> <scrutinees>)
              with <exn-patterns> -> <exn-actions>)
           with <val-exit> <val-ids> ->
              match <val-ids> with <val-patterns> -> <val-actions>

         In particular, the 'exit' in the value case ensures that the
         value actions run outside the try..with exception handler.
      *)
      let static_catch scrutinees val_ids handler =
        let id = Typecore.name_pattern "exn" (List.map fst exn_cases) in
        let static_exception_id = next_raise_count () in
        Lstaticcatch
          (Ltrywith (
             Lstaticraise (static_exception_id, scrutinees), id,
             Matching.for_trywith ~scopes kind e.exp_loc (Lvar id) exn_cases,
             kind),
           (static_exception_id, val_ids),
           handler,
           kind)
      in
      match arg, exn_cases with
      | {exp_desc = Texp_tuple argl}, [] ->
        assert (static_handlers = []);
        let mode = transl_exp_mode arg in
        Matching.for_multiple_match ~scopes kind e.exp_loc
          (transl_list ~scopes argl) mode val_cases partial
      | {exp_desc = Texp_tuple argl}, _ :: _ ->
          let val_ids =
            List.map
              (fun arg ->
                 Typecore.name_pattern "val" [],
                 (* CR ccasinghino will need adjustment when we allow void in
                    tuples *)
                 Typeopt.value_kind arg.exp_env arg.exp_type
              )
              argl
          in
          let lvars = List.map (fun (id, _) -> Lvar id) val_ids in
          let mode = transl_exp_mode arg in
          static_catch (transl_list ~scopes argl) val_ids
            (Matching.for_multiple_match ~scopes kind e.exp_loc
               lvars mode val_cases partial)
      | arg, [] ->
        assert (static_handlers = []);
        Matching.for_function ~scopes kind e.exp_loc
          None (transl_exp ~scopes None arg) val_cases partial
      | arg, _ :: _ ->
          let val_id = Typecore.name_pattern "val" (List.map fst val_cases) in
          let k = Typeopt.value_kind arg.exp_env arg.exp_type in
          static_catch [transl_exp ~scopes None arg] [val_id, k]
            (Matching.for_function ~scopes kind e.exp_loc
               None (Lvar val_id) val_cases partial)
  in
  List.fold_left (fun body (static_exception_id, val_ids, handler) ->
    Lstaticcatch (body, (static_exception_id, val_ids), handler, kind)
  ) lam_match static_handlers

and transl_letop ~scopes loc env let_ ands param case partial warnings =
  let rec loop prev_lam = function
    | [] -> prev_lam
    | and_ :: rest ->
        let left_id = Ident.create_local "left" in
        let right_id = Ident.create_local "right" in
        let op =
          transl_ident (of_location ~scopes and_.bop_op_name.loc) env
            and_.bop_op_type and_.bop_op_path and_.bop_op_val Id_value
        in
        let exp = transl_exp ~scopes None and_.bop_exp in
        let lam =
          bind Strict right_id exp
            (Lapply{
               ap_loc = of_location ~scopes and_.bop_loc;
               ap_func = op;
               ap_args=[Lvar left_id; Lvar right_id];
               ap_region_close=Rc_normal;
               ap_mode=alloc_heap;
               ap_tailcall = Default_tailcall;
               ap_inlined = Default_inlined;
               ap_specialised = Default_specialise;
               ap_probe=None;
             })
        in
        bind Strict left_id prev_lam (loop lam rest)
  in
  let op =
    transl_ident (of_location ~scopes let_.bop_op_name.loc) env
      let_.bop_op_type let_.bop_op_path let_.bop_op_val Id_value
  in
  let exp = loop (transl_exp ~scopes None let_.bop_exp) ands in
  let func =
    let return_kind = value_kind case.c_rhs.exp_env case.c_rhs.exp_type in
    let curry = More_args { partial_mode = Alloc_mode.global } in
    let (kind, params, return, _region), body =
      event_function ~scopes case.c_rhs
        (function repr ->
           transl_curried_function ~scopes case.c_rhs.exp_loc return_kind
             repr ~region:true ~curry partial warnings param [case])
    in
    let attr = default_function_attribute in
    let loc = of_location ~scopes case.c_rhs.exp_loc in
    let body = maybe_region body in
    lfunction ~kind ~params ~return ~body ~attr ~loc
              ~mode:alloc_heap ~region:true
  in
  Lapply{
    ap_loc = of_location ~scopes loc;
    ap_func = op;
    ap_args=[exp; func];
    ap_region_close=Rc_normal;
    ap_mode=alloc_heap;
    ap_tailcall = Default_tailcall;
    ap_inlined = Default_inlined;
    ap_specialised = Default_specialise;
    ap_probe=None;
  }

(* Wrapper for class/module compilation,
   that can only return global values *)

let transl_exp ~scopes void_k exp =
  maybe_region (transl_exp ~scopes void_k exp)

let transl_let ~scopes ?in_structure rec_flag pat_expr_list =
  transl_let ~scopes ~add_regions:true ?in_structure rec_flag pat_expr_list

let transl_scoped_exp ~scopes void_k exp =
  maybe_region (transl_scoped_exp ~scopes void_k exp)

let transl_apply
      ~scopes ?tailcall ?inlined ?specialised ?position ?mode fn args loc =
  maybe_region (transl_apply
      ~scopes ?tailcall ?inlined ?specialised ?position ?mode fn args loc)

(* Error report *)

open Format

let report_error ppf = function
  | Free_super_var ->
      fprintf ppf
        "Ancestor names can only be used to select inherited methods"
  | Unreachable_reached ->
      fprintf ppf "Unreachable expression was reached"

let () =
  Location.register_error_of_exn
    (function
      | Error (loc, err) ->
          Some (Location.error_of_printer ~loc report_error err)
      | _ ->
        None
    )
