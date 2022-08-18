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

type unique_seen_reason =
  | Seen_as of Ident.t
  | Tuple_match_on_aliased_as of Ident.t * Ident.t

type error =
  | Seen_twice of Ident.t * expression * unique_seen_reason * unique_seen_reason
  | Not_owned_in_expression of Ident.t

exception Error of Location.t * Env.t * error

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
      | Tuple_field _, (Record_field _ | Construct_field _ | Variant_field _ | Array_field _) -> -1
      | (Record_field _ | Construct_field _ | Variant_field _ | Array_field _), Tuple_field _ -> 1
      | Record_field _, (Construct_field _ | Variant_field _ | Array_field _) -> -1
      | (Construct_field _ | Variant_field _ | Array_field _), Record_field _ -> 1
      | Construct_field _, (Variant_field _ | Array_field _) -> -1
      | (Variant_field _ | Array_field _), Construct_field _ -> 1
      | Variant_field _, Array_field _ -> -1
      | Array_field _, Variant_field _ -> 1
  end
  include T
  module Map = Map.Make(T)

  let to_string parent = function
    | Tuple_field i -> Printf.sprintf "%s.%i" parent i
    | Record_field s -> Printf.sprintf "%s.%s" parent s
    | Construct_field (s, i) -> Printf.sprintf "%s|%s.%i" parent s i
    | Variant_field l -> Printf.sprintf "%s|%s" parent l
    | Array_field i -> Printf.sprintf "%s.%i" parent i
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
    constraints: Mode.Uniqueness.t Ident.Map.t;
    (* Modevars that need to be constrained when an ident is not unique.
       This includes those of aliases, as well as mode variables
       created for projections. *)
  }

(* "match x with" will be interpreted with OneParent(x).
   "match e with" will be interpreted with NoParent.
   "match x, e with" will be interpreted with
     TupleParent([OneParent(x); NoParent], "x, e") *)
type parent =
  | NoParent
  | OneParent of Ident.t
  | TupleParent of Ident.t option list * expression
  (* The expression is used for an error message if the tuple is aliased. *)

let lookup_alias id uenv =
  match Ident.Map.find_opt id uenv.aliases with
  | Some alias -> alias
  | None -> id

(* Depth-first search of the children map, marking all modes as shared.
   We have to be careful as there can be cycles due to or-patterns:

   match x with | Cons(1, y) | y -> y

   Here y aliases x and y is a child of x. Cycle! *)
let force_shared id err uenv =
  let rec loop seen id err uenv =
    if List.memq id seen then seen else
      let _ = Option.iter
        (fun m -> match Mode.Uniqueness.submode (Amode Shared) m with
           | Ok () -> ()
           | Error () -> raise err)
        (Ident.Map.find_opt id uenv.constraints) in
      let cs = match Ident.Map.find_opt id uenv.children with
        | None -> Projection.Map.empty
        | Some projs -> projs in
      Projection.Map.fold (fun _ id' seen -> loop seen id' err uenv) cs (id::seen) in
  let _ = loop [] id err uenv in ()

(* Get the highest point in the children tree where the uniqueness fails.
   If we have not recursed into children yet, we found a reason why uniqueness
   failed for an id or a parent: In this case that parent is the highest point.
   If we have recursed already, we have not failed at id, which means that all
   parents of id are fine. Then id is the highest point. *)
let get_subject ~has_recursed reason id uenv =
  if has_recursed then id else
    let rid = match reason with
      | Seen_as(rid) -> rid
      | Tuple_match_on_aliased_as(rid, _) -> rid in
    lookup_alias rid uenv

let rec mark_seen_ ~has_recursed ~visit_children id reason exp uenv =
  let id = lookup_alias id uenv in
  let _ = if Ident.Set.mem id uenv.owned then () else
    let err = Error(exp.exp_loc, exp.exp_env, Not_owned_in_expression(id)) in
    force_shared id err uenv in
  match Ident.Map.find_opt id uenv.last_seen with
  | None ->
    if visit_children then
      let uenv = { uenv with last_seen = Ident.Map.add id (exp, reason) uenv.last_seen } in
      let children = match Ident.Map.find_opt id uenv.children with
        | None -> Projection.Map.empty
        | Some projs -> projs in
      Projection.Map.fold (fun _ c uenv -> mark_seen_ ~has_recursed:true ~visit_children:true c reason exp uenv) children uenv
    else uenv
  | Some (exp', reason') ->
    let err = Error(exp.exp_loc, exp.exp_env, Seen_twice(id, exp', reason, reason')) in
    let subject = (get_subject ~has_recursed reason' id uenv) in
    force_shared subject err uenv; uenv
let mark_seen id reason exp uenv =
  mark_seen_ ~has_recursed:false ~visit_children:true id reason exp uenv
let mark_seen_no_children id reason exp uenv =
  mark_seen_ ~has_recursed:false ~visit_children:false id reason exp uenv

let mark_owned x uenv =
  { uenv with owned = Ident.Set.add x uenv.owned }

let imply_owned parent id uenv =
  if Ident.Set.mem parent uenv.owned
    then mark_owned id uenv else uenv

let without_owned f uenv =
  let uenv' = f { uenv with owned = Ident.Set.empty } in
  { uenv' with owned = uenv.owned }

let add_mproj parent mproj id uenv =
  let parent = lookup_alias parent uenv in
  let uenv = imply_owned parent id uenv in
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
  let name = match mproj with
    | Some proj -> Projection.to_string (Ident.name parent) proj
    | None -> Ident.name parent in
  let id = Ident.create_local name in
  id, add_mproj parent mproj id uenv

let add_mode id mode exp uenv =
  let id = lookup_alias id uenv in
  let err exp' reason' =  Error(exp.exp_loc, exp.exp_env, Seen_twice(id, exp', Seen_as(id), reason')) in
  let id_mode = match Ident.Map.find_opt id uenv.constraints with
    | None -> let id_mode, _ = Mode.Uniqueness.newvar_below mode in id_mode
    | Some id_mode -> match Mode.Uniqueness.submode id_mode mode with
      | Ok () -> id_mode
      | Error () -> match Ident.Map.find_opt id uenv.last_seen with
        | None -> assert false (* Invariant: id_mode is shared only when seen at least twice. *)
        | Some (exp', reason') -> raise (err exp' reason') in
  let uenv = { uenv with constraints = Ident.Map.add id id_mode uenv.constraints } in
  match Ident.Map.find_opt id uenv.last_seen with
  | None -> uenv
  | Some (exp', reason') -> force_shared id (err exp' reason') uenv; uenv

let pat_var id parent mproj uenv =
  match parent with
  | NoParent -> mark_owned id uenv
  | OneParent(p) -> add_mproj p mproj id uenv
  | TupleParent(ps, exp) ->
      let uenv = mark_owned id uenv in
      (* Mark all ps as seen, as we bind the tuple to a variable. *)
      List.fold_left (fun uenv p ->
          match p with
          | None -> uenv
          | Some p -> mark_seen p (Tuple_match_on_aliased_as(p, id)) exp uenv) uenv ps

(* We interpret "match x with | A y" as
     pat_to_map (A y) x uenv
     = pat_to_map_ y x (Some (Construct_field A 0)) uenv
     = add_mproj x (Some (Construct_field A 0)) y uenv
     = { uenv with "x -> (Construct_field A 0 -> y)" }

  Invariants:
   - mproj == None if parent != OneParent(_, _) **)
let rec pat_to_map_ (pat : Typedtree.pattern) parent mproj uenv =
  match pat.pat_desc with
  | Tpat_any -> uenv
  | Tpat_var(id, _, _) ->
      pat_var id parent mproj uenv
  | Tpat_alias(pat',id, _, _) ->
      let uenv = pat_var id parent mproj uenv
      in pat_to_map_ pat' (OneParent id) None uenv
  | Tpat_constant(_) -> uenv
  | Tpat_tuple(ps) ->
      pat_proj ~handle_tuple:(fun ps' ->
          (* We matched a tuple against a tuple parent and descend into each case *)
          List.fold_left2
            (fun uenv pat' p ->
                let parent =
                  match p with
                  | None -> NoParent
                  | Some p -> OneParent(p) in
                pat_to_map_ pat' parent None uenv)
            uenv ps ps'
        ) ~extract_pat:Fun.id ~mk_proj:(fun i _ -> Projection.Tuple_field i) parent mproj ps uenv
  | Tpat_construct(lbl, _, ps) ->
      pat_proj ~extract_pat:Fun.id ~mk_proj:(fun i _ -> Projection.Construct_field(Longident.last lbl.txt, i)) parent mproj ps uenv
  | Tpat_variant(lbl, mpat, _) -> begin
      match mpat with
      | Some pat' ->
          let parent, uenv = match mproj, parent with
            | Some _, OneParent p ->
                let id, uenv = add_anon_mproj p mproj uenv in OneParent(id), uenv
            | _, _ -> parent, uenv in
          pat_to_map_ pat' parent (Some (Projection.Variant_field lbl)) uenv
      | None -> uenv
      end
  | Tpat_record((ps : (_ * _ * _) list), _) ->
      pat_proj ~extract_pat:(fun (_, _, pat) -> pat) ~mk_proj:(fun _ (_, l, _) -> Projection.Record_field(l.lbl_name)) parent mproj ps uenv
  | Tpat_array(ps) ->
      pat_proj ~extract_pat:Fun.id ~mk_proj:(fun i _ -> Projection.Array_field i) parent mproj ps uenv
  | Tpat_lazy(pat') -> pat_to_map_ pat' parent mproj uenv
  | Tpat_or(a, b, _) ->
      let uenv = pat_to_map_ a parent mproj uenv in
      pat_to_map_ b parent mproj uenv
and pat_proj : 'a. ?handle_tuple:_ -> extract_pat:('a -> _) -> mk_proj:(_ -> 'a -> _) -> _ -> _ -> 'a list -> _ -> _ =
  fun ?(handle_tuple = fun _ -> assert false) ~extract_pat ~mk_proj parent mproj ps uenv ->
    match ps with
    | [] -> uenv (* Do not create a new name for singletons *)
    | _ ->
      match parent with
      | NoParent ->
          List.fold_left (fun uenv pat' -> pat_to_map_ (extract_pat pat') parent None uenv) uenv ps
      | OneParent(p) ->
          let id, uenv = add_anon_mproj p mproj uenv in
          let uenv, _ =
            List.fold_left
              (fun (uenv, i) patlike ->
                let uenv = pat_to_map_ (extract_pat patlike) (OneParent id) (Some (mk_proj i patlike)) uenv in
                let i = i + 1 in
                uenv, i)
              (uenv, 0) ps
          in uenv
      | TupleParent(ps', _) -> handle_tuple ps'

let pat_to_map (pat : Typedtree.pattern) parent uenv =
  pat_to_map_ pat parent None uenv

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

let rec check_uniqueness_exp_ exp uenv =
  match exp.exp_desc with
  | Texp_ident(p, _, _, _, mode) -> begin
      match ident_option_from_path p with
      | Some id ->
        let uenv = add_mode id mode.uniqueness exp uenv in
        mark_seen id (Seen_as id) exp uenv
      | None -> uenv
      end
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
      let parent, uenv = exp_to_parent ~check:true e uenv in
      check_uniqueness_comp_cases parent cs uenv
  | Texp_try(e, cs) ->
      let uenv = check_uniqueness_exp_ e uenv in
      check_uniqueness_cases NoParent cs uenv
  | Texp_tuple(es) ->
      List.fold_left (fun uenv e -> check_uniqueness_exp_ e uenv) uenv es
  | Texp_construct(_, _, es) ->
      List.fold_left (fun uenv e -> check_uniqueness_exp_ e uenv) uenv es
  | Texp_variant(_, None) -> uenv
  | Texp_variant(_, Some e) -> check_uniqueness_exp_ e uenv
  | Texp_record { fields; extended_expression } -> begin
      let check_fields uenv =
        Array.fold_left (fun uenv f -> match f with
          | _, Kept _ -> uenv
          | _, Overridden (_, e) -> check_uniqueness_exp_ e uenv) uenv fields in
      let check_fields_with_parent parent uenv =
        Array.fold_left (fun uenv field -> match field with
            | l, Kept _ ->
                let id, uenv = add_anon_mproj parent (Some (Projection.Record_field l.lbl_name)) uenv in
                (* TODO Add new mode_vars in type checking; is this done? *)
                mark_seen id (Seen_as id) exp uenv
            | _, Overridden (_, e) -> check_uniqueness_exp_ e uenv) uenv fields in
      match extended_expression with
      | Some exp when has_unique_attr_texp exp ->
        let parent, uenv = path_to_parent ~check:true exp uenv in
        begin
          match parent with
          | None -> check_fields uenv
          | Some parent ->
              let uenv = check_fields_with_parent parent uenv in
              mark_seen_no_children parent (Seen_as parent) exp uenv end
      | Some exp -> (* Normal record-with: check all subexpressions *)
          let uenv = check_fields uenv in check_uniqueness_exp_ exp uenv
      | None -> check_fields uenv
      end
  | Texp_field(e, _, l, mode) -> begin
      match (path_to_parent ~check:true e uenv : Ident.t option * unique_env) with
      | Some parent, uenv ->
        let id, uenv = add_anon_mproj parent (Some (Projection.Record_field l.lbl_name)) uenv in
        let uenv = add_mode id mode.uniqueness exp uenv in
        mark_seen id (Seen_as id) exp uenv
      | None, uenv -> uenv
    end
  | Texp_setfield(exp', _, _, e) ->
      let _, uenv = path_to_parent ~check:true exp' uenv in
      check_uniqueness_exp_ e uenv
  | Texp_array(es) ->
      List.fold_left (fun uenv e -> check_uniqueness_exp_ e uenv) uenv es
  | Texp_ifthenelse(if', then', else_opt) ->
      let _, uenv = path_to_parent ~check:true if' uenv in
      begin match else_opt with
      | Some else' -> check_uniqueness_parallel [then'; else'] uenv
      | None -> check_uniqueness_exp_ then' uenv
      end
  | Texp_sequence(e, e') ->
      let uenv = check_uniqueness_exp_ e uenv in
      check_uniqueness_exp_ e' uenv
  | Texp_while(e, e') ->
      without_owned (fun uenv ->
          let uenv = check_uniqueness_exp_ e uenv in
          check_uniqueness_exp_ e' uenv)
        uenv
  | Texp_list_comprehension(e, cs) ->
      without_owned (fun uenv ->
          let uenv = check_uniqueness_exp_ e uenv in
          check_uniqueness_comprehensions cs uenv)
        uenv
  | Texp_arr_comprehension(e, cs) ->
      without_owned (fun uenv ->
          let uenv = check_uniqueness_exp_ e uenv in
          check_uniqueness_comprehensions cs uenv)
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
      List.fold_left (fun uenv (_, _, e) ->
          check_uniqueness_exp_ e uenv
        ) uenv ls
  | Texp_letmodule _ -> uenv (* TODO *)
  | Texp_letexception(_, e) -> check_uniqueness_exp_ e uenv
  | Texp_assert e -> check_uniqueness_exp_ e uenv
  | Texp_lazy e -> check_uniqueness_exp_ e uenv
  | Texp_object _ -> uenv (* TODO *)
  | Texp_pack _ -> uenv (* TODO *)
  | Texp_letop {let_;ands;param;body} ->
      (* CR-soon anlorenzen for lwhite: Is it necessary to mark param as seen? *)
      let uenv = mark_seen param (Seen_as param) exp uenv in
      let uenv = check_uniqueness_binding_op let_ exp uenv in
      let uenv = List.fold_left (fun uenv bop ->
          check_uniqueness_binding_op bop exp uenv) uenv ands in
      check_uniqueness_cases (OneParent param) [body] uenv
  | Texp_unreachable -> uenv
  | Texp_extension_constructor _ -> uenv
  | Texp_open _ -> uenv (* TODO *)
  | Texp_probe { handler } -> check_uniqueness_exp_ handler uenv
  | Texp_probe_is_enabled _ -> uenv

and path_to_parent : check:bool -> Typedtree.expression -> unique_env -> Ident.t option * unique_env = fun ~check exp uenv ->
  match exp.exp_desc with
  | Texp_ident(p, _, _, _, mode) ->
      let id = ident_option_from_path p in
      let uenv = match id with | Some id -> add_mode id mode.uniqueness exp uenv | None -> uenv in
      id, uenv
  | Texp_field(e, _, l, mode) -> begin
      match path_to_parent ~check e uenv with
      | Some parent, uenv ->
          let id, uenv = add_anon_mproj parent (Some (Projection.Record_field l.lbl_name)) uenv in
          let uenv = add_mode id mode.uniqueness exp uenv in
          Some id, uenv
      | None, uenv -> None, uenv end
  | _ -> None, if check then check_uniqueness_exp_ exp uenv else uenv
and exp_to_parent ~check exp uenv =
  match exp.exp_desc with
  | Texp_tuple(es) ->
      let swap (x, y) = (y, x) in
      let uenv, ps = List.fold_left_map (fun uenv e -> swap (path_to_parent ~check e uenv)) uenv es in
      TupleParent(ps, exp), uenv
  | _ ->
      match path_to_parent ~check exp uenv with
      | Some id, uenv -> OneParent id, uenv
      | None, uenv -> NoParent, uenv

and check_uniqueness_value_bindings_ vbs uenv =
  let uenv = List.fold_left
      (fun uenv vb ->
         let parent, uenv = exp_to_parent ~check:false vb.vb_expr uenv in
         pat_to_map vb.vb_pat parent uenv)
      uenv vbs in
  List.fold_left (fun uenv vb -> snd (exp_to_parent ~check:true vb.vb_expr uenv)) uenv vbs

and check_uniqueness_parallel es uenv =
  let orig_last_seen = uenv.last_seen in
  let orig_modes = uenv.constraints in
  let uenv, uenvs = List.fold_left_map (fun uenv e ->
      let uenv = check_uniqueness_exp_ e {
          (* Maps that simply record information are scoped by idents and can be accumulated. *)
          children = uenv.children; owned = uenv.owned; aliases = uenv.aliases;
          last_seen = orig_last_seen; (* Do not share last_seens.  *)
          constraints = Ident.Map.map (* Do not share constraints. *)
              (fun m -> let v, _ = Mode.Uniqueness.newvar_below m in v) orig_modes } in
      uenv, (uenv.last_seen, uenv.constraints)) uenv es in
  let last_seens, modes = List.split uenvs in
  { uenv with
    last_seen = List.fold_left (fun a b -> Ident.Map.union (fun _ x _ -> Some x) a b)
        Ident.Map.empty last_seens;
    constraints = List.fold_left (fun a b -> Ident.Map.union (fun _ x y -> Some (Mode.Uniqueness.join [x; y])) a b)
        Ident.Map.empty modes }

and check_uniqueness_cases_
  : 'a. ('a Typedtree.general_pattern -> parent -> unique_env -> unique_env)
    -> parent -> 'a case list -> unique_env -> unique_env =
  fun ptm parent cs uenv ->
  let uenv = List.fold_left (fun uenv c -> ptm c.c_lhs parent uenv) uenv cs in
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
  List.fold_left (fun uenv c ->
      let uenv = match c.guard with
        | None -> uenv
        | Some e -> check_uniqueness_exp_ e uenv in
      List.fold_left (fun uenv c ->
          match c with
          | From_to(_, _, e1, e2, _) -> check_uniqueness_exp_ e1 (check_uniqueness_exp_ e2 uenv)
          | In(_, e) -> check_uniqueness_exp_ e uenv) uenv c.clauses)
    uenv cs

and check_uniqueness_binding_op bo exp uenv =
  let uenv = match ident_option_from_path bo.bop_op_path with
    | Some id -> mark_seen id (Seen_as id) exp uenv
    | None -> uenv in
  check_uniqueness_exp_ bo.bop_exp uenv


let check_uniqueness_exp exp =
  let _ = check_uniqueness_exp_ exp
      { last_seen = Ident.Map.empty;
        children = Ident.Map.empty;
        owned = Ident.Set.empty;
        aliases = Ident.Map.empty;
        constraints = Ident.Map.empty; }
  in ()

let check_uniqueness_value_bindings vbs =
  let _ = check_uniqueness_value_bindings_ vbs
      { last_seen = Ident.Map.empty;
        children = Ident.Map.empty;
        owned = Ident.Set.empty;
        aliases = Ident.Map.empty;
        constraints = Ident.Map.empty; }
  in ()

let report_error ~loc = function
  | Not_owned_in_expression id ->
    Location.errorf ~loc
      "The identifier@ %s was inferred to be unique and thus can not be@ \
        used in a context where unique use is not guaranteed."
      (Ident.name id)
  | Seen_twice(id, other, r1, r2) ->
    (* TODO: incorporate expression into the error *)
    let get_reason r place = match r with
      | Seen_as id' ->
        if Ident.same id id' then Format.dprintf ""
        else Format.dprintf
                " It was seen %s because %s is a parent or alias of %s."
                place (Ident.name id') (Ident.name id)
      | Tuple_match_on_aliased_as(id', alias) ->
        if Ident.same id id'
        then Format.dprintf
                " It was seen %s because %s refers to a tuple containing %s."
                place (Ident.name alias) (Ident.name id')
        else Format.dprintf
                " It was seen %s because %s refers to a tuple@ \
                containing %s, which is a parent or alias of %s."
                place (Ident.name alias) (Ident.name id') (Ident.name id) in
    Location.errorf ~loc ~sub:[Location.msg ~loc:other.exp_loc "@[%t @]" (get_reason r2 "previously")]
      "@[%s is used uniquely so cannot be used twice.%t%s @]"
      (Ident.name id) (get_reason r1 "here") " It was seen previously at:"

let report_error ~loc env err =
  Printtyp.wrap_printing_env ~error:true env
    (fun () -> report_error ~loc err)

let () =
  Location.register_error_of_exn
    (function
      | Error (loc, env, err) ->
          Some (report_error ~loc env err)
      | _ ->
          None
    )
