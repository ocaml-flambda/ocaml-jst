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

open Asttypes
open Types
open Typedtree
module Uniqueness_mode = Btype.Uniqueness_mode

type unique_seen_reason =
  | Seen_as of Ident.t
  | Tuple_match_on_aliased_as of Ident.t * Ident.t

type unique_error =
  | Seen_twice of Ident.t * expression * unique_seen_reason * unique_seen_reason
  | Not_owned_in_expression of Ident.t

exception Unique_error of Location.t * Env.t * unique_error

let has_unique_attr loc attrs =
  match Builtin_attributes.has_unique attrs with
  | Ok l -> l
  | Error () ->
      raise(Typetexp.Error(loc, Env.empty, Unique_not_enabled))

let has_unique_attr_texp (texp : Typedtree.expression) =
  has_unique_attr texp.exp_loc texp.exp_attributes

module Projection = struct
  module T = struct
    type t =
      | Tuple_field of int
      | Record_field of string
      | Construct_field of string * int
      | Variant_field of label
      | Array_field of int

    let compare t1 t2 = match t1, t2 with
      | Tuple_field i, Tuple_field j -> Int.compare i j
      | Record_field l1, Record_field l2 -> String.compare l1 l2
      | Construct_field(l1, i), Construct_field(l2, j) ->
        begin match String.compare l1 l2 with
        | 0 -> Int.compare i j
        | i -> i end
      | Variant_field l1, Variant_field l2 -> String.compare l1 l2
      | Array_field i, Array_field j -> Int.compare i j
      | Tuple_field _, Record_field _ -> -1
      | Tuple_field _, Construct_field _ -> -1
      | Tuple_field _, Variant_field _ -> -1
      | Tuple_field _, Array_field _ -> -1
      | Record_field _, Construct_field _ -> -1
      | Record_field _, Variant_field _ -> -1
      | Record_field _, Array_field _ -> -1
      | Construct_field _, Variant_field _ -> -1
      | Construct_field _, Array_field _ -> -1
      | Variant_field _, Array_field _ -> -1
      | _, _ -> 1
  end
  include T
  module Map = Map.Make(T)
end

(* Whenever an identifier or its parent/child was seen twice,
   we want to report an error message showing both locations.

   Example: match x with | A y ->  ... y ... x ... (for unique x)
   should error with the locations of x and y.

   Example: match x with | A y ->
              match x with | A z ->  ... y ... z ... (for unique x)
   should error with the locations of y and z.

   We thus store the children of each variable (e.g. y for x)
   as well as aliases that were introduced (e.g. z for y).
   To be able to find aliases like z and y, we keep the children
   by their projections out of the parent.
   When we see y, we mark y as seen. When we see z, we mark y as seen.
   When we see x, we mark x and y as seen. If y was already marked,
   it must have been seen already and we fail. *)
type unique_env =
  { last_seen: (expression * unique_seen_reason) Ident.Map.t;
    (* Match a representing ident to a reason where it was last seen. *)
    children: Ident.t Projection.Map.t Ident.Map.t;
    (* The direct children of an identifier (when applying a projection).
       The children are always representing idents. *)
    owned: Ident.Set.t;
    (* The representing idents that can be used uniquely at the moment.
       We do not delete them from the map once we have seen them,
       but only when we enter a section where they can not be used:
       e.g. a function closure or a for-loop.
       TODO: this is temporary until we implement closures by locks. *)
    aliases: Ident.t Ident.Map.t;
    (* If several idents refer to the same structure in memory,
        they are mapped to the "representing" ident x that we saw first.
        We do not map x to itself in general (but we do for function params
        as it is more convenient there). *)
    constraints: Types.uniqueness Types.mode list Ident.Map.t;
    (* Modevars that need to be constrained when an ident is not unique.
       This includes those of aliases, as well as mode variables
       created for projections. *)
  }

(* A tuple pattern can have one parent per element of the tuple.*)
type parent =
  | NoParent
  | OneParent of Ident.t
  | TupleParent of parent list * expression
  (* The expression is used for an error message if the tuple is aliased. *)

let lookup_alias id uenv =
  match Ident.Map.find_opt id uenv.aliases with
  | Some alias -> alias
  | None -> id

(* Depth-first search of the children map, marking all modes as shared.
   We have to be careful as there can be cycles due to or-patterns:

   match x with | Cons(1, y) | y -> y

   Here y aliases x and y is a child of x. Cycle! *)
let rec mark_shared_ seen id err uenv =
  if List.memq id seen then seen else
  let ms = match Ident.Map.find_opt id uenv.constraints with
    | None -> []
    | Some ms -> ms in
  List.iter
    (fun m -> match Uniqueness_mode.submode (Amode Shared) m with
       | Ok () -> ()
       | Error () -> raise err) ms;
  let cs = match Ident.Map.find_opt id uenv.children with
    | None -> []
    | Some projs -> Projection.Map.bindings projs in
  List.fold_left (fun seen (_, id') -> mark_shared_ seen id' err uenv) (id::seen) cs
let mark_shared id err uenv =
  let _ = mark_shared_ [] id err uenv in ()

(* Get the highest point in the children tree where the uniqueness fails.
   If we have not recursed into children yet, we found a reason why uniqueness
   failed for a id or a parent: In this case that parent is the highest point.
   If we have recursed already, we have not failed at id, which means that all
   parents of id are fine. Then id is the highest point. *)
let get_subject has_recursed reason id uenv =
  if has_recursed then id else
    let rid = match reason with
      | Seen_as(rid) -> rid
      | Tuple_match_on_aliased_as(rid, _) -> rid in
    lookup_alias rid uenv

let rec mark_seen_ has_recursed visit_children id reason exp uenv =
  let id = lookup_alias id uenv in
  let _ = if Ident.Set.mem id uenv.owned then () else
    let err = Unique_error(exp.exp_loc, exp.exp_env, Not_owned_in_expression(id)) in
    mark_shared id err uenv in
  match Ident.Map.find_opt id uenv.last_seen with
  | None ->
    if visit_children then
      let uenv = { uenv with last_seen = Ident.Map.add id (exp, reason) uenv.last_seen } in
      let children = match Ident.Map.find_opt id uenv.children with
        | None -> []
        | Some projs -> Projection.Map.bindings projs in
      List.fold_left (fun uenv (_, c) -> mark_seen_ true true c reason exp uenv) uenv children
    else uenv
  | Some (exp', reason') ->
    let err = Unique_error(exp.exp_loc, exp.exp_env, Seen_twice(id, exp', reason, reason')) in
    mark_shared (get_subject has_recursed reason' id uenv) err uenv; uenv
let mark_seen id reason exp uenv =
  mark_seen_ false true id reason exp uenv
let mark_seen_no_children id reason exp uenv =
  mark_seen_ false false id reason exp uenv

let add_mproj parent mproj id uenv =
  let parent = lookup_alias parent uenv in
  let uenv = if Ident.Set.mem parent uenv.owned
    then { uenv with owned = Ident.Set.add id uenv.owned }
    else uenv in
  match mproj with
  | None -> { uenv with aliases = Ident.Map.add id parent uenv.aliases }
  | Some proj -> match Ident.Map.find_opt parent uenv.children with
    | None ->
      { uenv with children = Ident.Map.add parent (Projection.Map.singleton proj id) uenv.children }
    | Some projs -> match Projection.Map.find_opt proj projs with
      | None ->
        { uenv with children = Ident.Map.add parent (Projection.Map.add proj id projs) uenv.children }
      | Some old ->
        { uenv with aliases = Ident.Map.add id old uenv.aliases }

let add_anon_mproj parent mproj uenv =
  let id = Ident.create_local "anon" in
  id, add_mproj parent mproj id uenv

let add_mode id mode uenv =
  let id = lookup_alias id uenv in
  let ms = match Ident.Map.find_opt id uenv.constraints with
    | None -> []
    | Some ms -> ms in
  { uenv with constraints = Ident.Map.add id (mode :: ms) uenv.constraints }

let rec mark_tuple_parent_seen id ps exp uenv =
  match ps with
  | [] -> uenv
  | NoParent :: ps -> mark_tuple_parent_seen id ps exp uenv
  | (OneParent p) :: ps ->
    mark_tuple_parent_seen id ps exp
      (mark_seen p (Tuple_match_on_aliased_as(p, id)) exp uenv)
  | (TupleParent (ps', exp')) :: ps ->
    mark_tuple_parent_seen id ps exp (mark_tuple_parent_seen id ps' exp' uenv)

let mark_owned x uenv =
  { uenv with owned = Ident.Set.add x uenv.owned }

let without_owned f uenv =
  let uenv' = f { uenv with owned = Ident.Set.empty } in
  { uenv' with owned = uenv.owned }

(* "match x with | A y" will be interpreted with OneParent(x) and pat A y.
   "match e with | A y" will be interpreted with NoParent and pat A y.
   "match x, e with | pat" will be interpreted with TupleParent(OneParent(x), NoParent) *)
let rec pat_to_map (pat : Typedtree.pattern) parent uenv =
  pat_to_map_ pat parent None uenv

(* We interpret "match x with | A y" as
     pat_to_map (A y) x uenv
     = pat_to_map_ y x (Some (Construct_field A 0)) uenv
     = add_mproj x (Some (Construct_field A 0)) y uenv
     = { uenv with "x -> (Construct_field A 0 -> y)" }

  Invariants:
   - mproj == None if parent != OneParent(_, _) *)
and pat_to_map_ (pat : Typedtree.pattern) parent mproj uenv =
  match pat.pat_desc with
  | Tpat_any -> uenv
  | Tpat_var(id, _) -> begin
    match parent with
    | NoParent -> uenv
    | OneParent(p) -> add_mode id pat.pat_mode.uniqueness
                        (add_mproj p mproj id uenv)
    | TupleParent(ps, exp) -> mark_tuple_parent_seen id ps exp uenv end
  | Tpat_alias(pat',id, _) ->
    let uenv = match parent with
      | NoParent -> uenv
      | OneParent(p) -> add_mode id pat.pat_mode.uniqueness
                          (add_mproj p mproj id uenv)
      | TupleParent(ps, exp) -> mark_tuple_parent_seen id ps exp uenv
    in pat_to_map pat' (OneParent id) uenv
  | Tpat_constant(_) -> uenv
  | Tpat_tuple(ps) -> begin
      match ps with | [] -> uenv | _ ->
      match parent with
      | NoParent ->
        List.fold_left (fun uenv pat' -> pat_to_map pat' parent uenv) uenv ps
      | OneParent(p) ->
        let p, uenv = add_anon_mproj p mproj uenv in
        List.fold_left2
          (fun uenv pat' i ->
            pat_to_map_ pat' (OneParent p) (Some (Projection.Tuple_field i)) uenv)
          uenv ps (List.init (List.length ps) Fun.id)
      | TupleParent(ps', _) ->
        List.fold_left2
          (fun uenv pat' p -> pat_to_map pat' p uenv)
          uenv ps ps'
      end
  | Tpat_construct(lbl, _, ps) -> begin
      match ps with | [] -> uenv | _ ->
      match parent with
      | NoParent ->
        List.fold_left (fun uenv pat' -> pat_to_map pat' parent uenv) uenv ps
      | OneParent(p) ->
        let p, uenv = add_anon_mproj p mproj uenv in
        List.fold_left2
          (fun uenv pat' i ->
             pat_to_map_ pat' (OneParent p)
              (Some (Projection.Construct_field(Longident.last lbl.txt, i)))
              uenv)
          uenv ps (List.init (List.length ps) Fun.id)
      | TupleParent _ -> assert false
    end
  | Tpat_variant(lbl, mpat, _) -> begin
      match mpat with
      | Some pat' -> let parent, uenv = match mproj, parent with
        | Some _, OneParent p ->
          let p, uenv = add_anon_mproj p mproj uenv in OneParent(p), uenv
        | _, _ -> parent, uenv in
        pat_to_map_ pat' parent (Some (Projection.Variant_field lbl)) uenv
      | None -> uenv
      end
  | Tpat_record(ps, _) -> begin
      match ps with | [] -> uenv | _ ->
      match parent with
      | NoParent ->
        List.fold_left (fun uenv (_, _, pat') -> pat_to_map pat' parent uenv) uenv ps
      | OneParent(p) ->
        let p, uenv = add_anon_mproj p mproj uenv in
        List.fold_left
          (fun uenv (_ , l, pat') ->
             pat_to_map_ pat' (OneParent p)
               (Some (Projection.Record_field l.lbl_name)) uenv)
          uenv ps
      | TupleParent _ -> assert false
    end
  | Tpat_array(ps) -> begin
      match ps with | [] -> uenv | _ ->
      match parent with
      | NoParent ->
        List.fold_left (fun uenv pat' -> pat_to_map pat' parent uenv) uenv ps
      | OneParent(p) ->
        let p, uenv = add_anon_mproj p mproj uenv in
        List.fold_left2
          (fun uenv pat' i ->
              pat_to_map_ pat' (OneParent p) (Some (Projection.Array_field i)) uenv)
          uenv ps (List.init (List.length ps) Fun.id)
      | TupleParent _ -> assert false
    end
  | Tpat_lazy(pat') -> pat_to_map pat' parent uenv
  | Tpat_or(a, b, _) ->
    pat_to_map a parent (pat_to_map b parent uenv)

(* We ignore exceptions in uniqueness analysis. *)
let comp_pat_to_map
      (pat : Typedtree.computation Typedtree.general_pattern) parent uenv =
  match split_pattern pat with
  | Some pat', _ -> pat_to_map pat' parent uenv
  | None, _ -> uenv

let ident_option_from_path p =
  match p with
  | Path.Pident id -> Some id
  | Path.Pdot _ -> None (* Pdot's can not be unique *)
  | Path.Papply _ -> assert false

let mark_if_ident p exp uenv =
  match ident_option_from_path p with
  | Some id -> mark_seen id (Seen_as id) exp uenv
  | None -> uenv

let is_unique_variable_opt exp_opt =
  match exp_opt with
  | Some ({ exp_desc = Texp_ident(p, _, _, _) } as exp') ->
      begin match ident_option_from_path p with
      | Some id -> Some (id, has_unique_attr_texp exp')
      | None -> None
      end
  | _ -> None

let rec exp_to_parent exp =
  match exp.exp_desc with
  | Texp_ident(p, _, _, _) -> begin
      match ident_option_from_path p with
      | Some id -> OneParent id
      | None -> NoParent end
  | Texp_tuple(es) -> TupleParent(List.map exp_to_parent es, exp)
  | _ -> NoParent

let rec check_uniqueness_exp exp =
  let _ = check_uniqueness_exp_ exp
    { last_seen = Ident.Map.empty;
      children = Ident.Map.empty;
      owned = Ident.Set.empty;
      aliases = Ident.Map.empty;
      constraints = Ident.Map.empty; }
  in ()
and check_uniqueness_exp_ exp uenv =
  match exp.exp_desc with
  | Texp_ident(p, _, _, _) -> mark_if_ident p exp uenv
  | Texp_constant _ -> uenv
  | Texp_let(_, vbs, exp') ->
      let uenv = check_uniqueness_value_bindings_ vbs uenv in
      check_uniqueness_exp_ exp' uenv
  | Texp_function { param; cases } ->
    without_owned (fun uenv ->
      check_uniqueness_cases (OneParent param) cases (mark_owned param uenv))
      uenv
  | Texp_apply(f, xs, _) ->
      let uenv = check_uniqueness_exp_ f uenv in
      List.fold_left (fun uenv (_, arg) -> match arg with
          | Arg e -> check_uniqueness_exp_ e uenv
          | Omitted _ -> uenv) uenv xs
  | Texp_match(e, cs, _) ->
    let uenv = check_uniqueness_parent_ e uenv in
    check_uniqueness_comp_cases (exp_to_parent e) cs uenv
  | Texp_try(e, cs) ->
    let uenv = check_uniqueness_exp_ e uenv in
    check_uniqueness_cases NoParent cs uenv
  | Texp_tuple(es) ->
      List.fold_left (fun uenv e -> check_uniqueness_exp_ e uenv) uenv es
  | Texp_construct(_, _, es) ->
      List.fold_left (fun uenv e -> check_uniqueness_exp_ e uenv) uenv es
  | Texp_variant(_, e_opt) -> begin
    match e_opt with
    | None -> uenv
    | Some e -> check_uniqueness_exp_ e uenv end
  | Texp_record { fields; extended_expression } -> begin
      match is_unique_variable_opt extended_expression with
      | Some (parent, is_unique_with) -> (* Record with 'with' on variable *)
        let uenv = Array.fold_left (fun uenv f -> match f with
            | l, Kept _ ->
                let id, uenv = add_anon_mproj parent (Some (Projection.Record_field l.lbl_name)) uenv in
                (* TODO: Add new mode_vars in type checking *)
                mark_seen id (Seen_as id) exp uenv
            | _, Overridden (_, e) -> check_uniqueness_exp_ e uenv) uenv fields in
        if is_unique_with (* We use the allocation and can not use it again. *)
          then mark_seen_no_children parent (Seen_as parent) exp uenv
          else uenv
      | None -> (* Normal record: check all subexpressions *)
        let uenv = Array.fold_left (fun uenv f -> match f with
            | _, Kept _ -> uenv
            | _, Overridden (_, e) -> check_uniqueness_exp_ e uenv) uenv fields in
        match extended_expression with
        | None -> uenv
        | Some e -> check_uniqueness_exp_ e uenv
      end
  | Texp_field(e, _, l) -> begin
      match is_unique_variable_opt (Some e) with
      (* TODO: Add new mode_vars in type checking *)
      | Some (parent, _) ->
        let id, uenv = add_anon_mproj parent (Some (Projection.Record_field l.lbl_name)) uenv in
        mark_seen id (Seen_as id) exp uenv (* TODO: Nicer Seen_as name for error messages *)
      | None -> check_uniqueness_exp_ e uenv
    end
  | Texp_setfield(exp', _, _, e) -> begin
      match is_unique_variable_opt (Some exp') with
      (* In t.x <- e, we do not mark the variable t as seen. *)
      (* TODO: Remove last_seen marker from t.x for nicer interface *)
      | Some _ -> check_uniqueness_exp_ e uenv
      | None -> check_uniqueness_exp_ exp' (check_uniqueness_exp_ e uenv)
    end
  | Texp_array(es) ->
      List.fold_left (fun uenv e -> check_uniqueness_exp_ e uenv) uenv es
  | Texp_ifthenelse(if', then', else_opt) ->
      let uenv = match is_unique_variable_opt (Some if') with
        | Some _ -> uenv
        | None -> check_uniqueness_exp_ if' uenv in
      begin match else_opt with
      | Some else' -> check_uniqueness_parallel [then'; else'] uenv
      | None -> check_uniqueness_exp_ then' uenv
      end
  | Texp_sequence(e, e') ->
      check_uniqueness_exp_ e' (check_uniqueness_exp_ e uenv)
  | Texp_while(e, e') ->
      without_owned (fun uenv ->
          check_uniqueness_exp_ e' (check_uniqueness_exp_ e uenv))
        uenv
  | Texp_list_comprehension(e, cs) ->
      without_owned (fun uenv ->
          check_uniqueness_comprehensions cs (check_uniqueness_exp_ e uenv))
        uenv
  | Texp_arr_comprehension(e, cs) ->
      without_owned (fun uenv ->
          check_uniqueness_comprehensions cs (check_uniqueness_exp_ e uenv))
        uenv
  | Texp_for(_, _, from', to', _, body) ->
      let uenv = check_uniqueness_exp_ from' uenv in
      let uenv = check_uniqueness_exp_ to' uenv in
      without_owned (check_uniqueness_exp_ body) uenv
  | Texp_send(e, _, _, _) ->
      check_uniqueness_exp_ e uenv
  | Texp_new _ -> uenv
  | Texp_instvar _ -> uenv
  | Texp_setinstvar(_, _, _, e) ->
      check_uniqueness_exp_ e uenv
  | Texp_override(_, ls) ->
      List.fold_left (fun u (_, _, e) ->
          check_uniqueness_exp_ e u
        ) uenv ls
  | Texp_letmodule _ -> uenv (* TODO *)
  | Texp_letexception(_, e) -> check_uniqueness_exp_ e uenv
  | Texp_assert e -> check_uniqueness_exp_ e uenv
  | Texp_lazy e -> check_uniqueness_exp_ e uenv
  | Texp_object _ -> uenv (* TODO *)
  | Texp_pack _ -> uenv (* TODO *)
  | Texp_letop _ -> uenv (* TODO *)
  | Texp_unreachable -> uenv
  | Texp_extension_constructor _ -> uenv
  | Texp_open _ -> uenv (* TODO *)
  | Texp_probe { handler } -> check_uniqueness_exp_ handler uenv
  | Texp_probe_is_enabled _ -> uenv

and check_uniqueness_parent_ exp uenv =
  match exp.exp_desc with
  | Texp_ident _ -> uenv
  | Texp_tuple(xs) ->
      List.fold_left (fun uenv e -> check_uniqueness_parent_ e uenv) uenv xs
  | _ -> check_uniqueness_exp_ exp uenv

and check_uniqueness_value_bindings vbs =
  let _ = check_uniqueness_value_bindings_ vbs
            { last_seen = Ident.Map.empty;
              children = Ident.Map.empty;
              owned = Ident.Set.empty;
              aliases = Ident.Map.empty;
              constraints = Ident.Map.empty; }
  in ()
and check_uniqueness_value_bindings_ vbs uenv =
  let uenv = List.fold_left
      (fun uenv vb -> pat_to_map vb.vb_pat (exp_to_parent vb.vb_expr) uenv)
      uenv vbs in
  List.fold_left (fun uenv vb -> check_uniqueness_parent_ vb.vb_expr uenv) uenv vbs

and check_uniqueness_parallel es uenv =
  let uenv, us = List.fold_left_map (fun u e ->
      let u' = check_uniqueness_exp_ e {u with last_seen = uenv.last_seen} in
      u', u'.last_seen) uenv es in
  { uenv with last_seen =
                List.fold_left
                  (fun a b -> Ident.Map.union (fun _ x _ -> Some x) a b)
                  Ident.Map.empty us }

and check_uniqueness_cases_
  : 'a. ('a Typedtree.general_pattern -> parent -> unique_env -> unique_env)
    -> parent -> 'a case list -> unique_env -> unique_env =
  fun ptm parent cs uenv ->
  let uenv = List.fold_left (fun u c -> ptm c.c_lhs parent u) uenv cs in
  (* We check all guards first, even if this will mark some variables as shared
     unnecessarily. This way we do not have to analyse which guards run when. *)
  let uenv = List.fold_left (fun uenv c -> match c.c_guard with
    | None -> uenv
    | Some g -> check_uniqueness_exp_ g uenv) uenv cs in
  check_uniqueness_parallel (List.map (fun c -> c.c_rhs) cs) uenv

and check_uniqueness_cases parent cs uenv =
  check_uniqueness_cases_ pat_to_map parent cs uenv
and check_uniqueness_comp_cases parent cs uenv =
  check_uniqueness_cases_ comp_pat_to_map parent cs uenv

and check_uniqueness_comprehensions cs uenv =
  List.fold_left (fun u c ->
      let u = match c.guard with
        | None -> u
        | Some e -> check_uniqueness_exp_ e u in
      List.fold_left (fun u c ->
          match c with
          | From_to(_, _, e1, e2, _) -> check_uniqueness_exp_ e1 (check_uniqueness_exp_ e2 u)
          | In(_, e) -> check_uniqueness_exp_ e u) u c.clauses)
    uenv cs
