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

(* Projections from parent to child in match statement. *)
module Projection = struct
  module T = struct
    type t =
      | Tuple_field of int
      | Record_field of string
      | Construct_field of string * int
      | Variant_field of label
      | Memory_address
      (* The memory of the allocation to be reused. This is a hack
         which makes sense since it behaves as the other children. *)

    let compare t1 t2 = match t1, t2 with
      | Tuple_field i, Tuple_field j -> Int.compare i j
      | Record_field l1, Record_field l2 -> String.compare l1 l2
      | Construct_field(l1, i), Construct_field(l2, j) ->
        begin match String.compare l1 l2 with
        | 0 -> Int.compare i j
        | i -> i end
      | Variant_field l1, Variant_field l2 -> String.compare l1 l2
      | Memory_address, Memory_address -> 0
      | Tuple_field _, (Record_field _ | Construct_field _ | Variant_field _ | Memory_address) -> -1
      | (Record_field _ | Construct_field _ | Variant_field _ | Memory_address), Tuple_field _ -> 1
      | Record_field _, (Construct_field _ | Variant_field _ | Memory_address) -> -1
      | (Construct_field _ | Variant_field _ | Memory_address), Record_field _ -> 1
      | Construct_field _, (Variant_field _ | Memory_address) -> -1
      | (Variant_field _ | Memory_address), Construct_field _ -> 1
      | Variant_field _, Memory_address -> -1
      | Memory_address, Variant_field _ -> 1
  end
  include T
  module Map = Map.Make(T)

  let to_string parent = function
    | Tuple_field i -> Printf.sprintf "%s.%i" parent i
    | Record_field s -> Printf.sprintf "%s.%s" parent s
    | Construct_field (s, i) -> Printf.sprintf "%s|%s.%i" parent s i
    | Variant_field l -> Printf.sprintf "%s|%s" parent l
    | Memory_address -> Printf.sprintf "%s (memory)" parent
end

(* New names to avoid polluting the Ident namespace. *)
module Uqid : sig
  type t
  module Map : Map.S with type key = t
  val fresh : string -> t
  val name : t -> string
end = struct
  module T = struct
    type t = { id : int; name : string }

    let compare t1 t2 = t1.id - t2.id
  end
  include T
  module Map = Map.Make(T)

  let stamp = ref 0

  let fresh name =
    let id = !stamp in
    stamp := id + 1; { id; name }

  let name t1 = t1.name
end

type relationship = Itself | Parent | Child

type err_id =
  | Ident of Ident.t
  | Field of err_id * string

type unique_seen_reason =
  | Seen_as of err_id
  | Tuple_match_on_aliased_as of err_id * Ident.t

type temporal = ThereBeforeHere | HereBeforeThere

type error =
  | Seen_twice of
      { here : Location.t; here_reason : unique_seen_reason;
        there : Location.t; there_reason : unique_seen_reason;
        temporal : temporal; there_is_of_here : relationship }

exception Error of error

module Occurrence : sig
  type t
  module Set : Set.S with type elt = t
  val fresh : Location.t -> unique_seen_reason -> Mode.Uniqueness.t -> t
  val force_shared : t -> (unit, unit) result
  val loc : t -> Location.t
  val reason : t -> unique_seen_reason
  val mode : t -> Mode.Uniqueness.t
  val relationship : t -> relationship
  val set_relationship : relationship -> t -> t
end = struct
  module T = struct
    type t =
      { id : int; loc : Location.t; reason : unique_seen_reason;
        mode : Mode.Uniqueness.t; relationship : relationship }

    let compare t1 t2 = t1.id - t2.id
  end
  include T
  module Set = Set.Make(T)

  let stamp = ref 0

  let fresh loc reason mode =
    let id = !stamp in
    stamp := id + 1;
    { id; loc; reason; mode; relationship = Itself }

  let force_shared t =
    Mode.Uniqueness.submode (Amode Shared) t.mode

  let loc t = t.loc
  let reason t = t.reason
  let mode t = t.mode
  let relationship t = t.relationship
  let set_relationship relationship t = { t with relationship }
end

(* We carry information to be able to report precise errors.
   When we see an ident for the second time, we have to make
   all previous occurrences (which happened in separate branches
   of the control flow) shared -- all of which can fail.
   If we see an ident again, we can only fail to make it shared
   at the current location -- and so we report just one previous location. *)
type occurrences =
  | One of Occurrence.Set.t
    (* One occurrence in the control-flow, but perhaps several
       in total (eg. in different branches) *)
  | Many of { loc : Location.t; reason : unique_seen_reason;
              relationship : relationship; children_marked : bool }
    (* If we see the ident used uniquely again,
       we want to report the location where it was consumed *)
  | PartlyUsed of { loc : Location.t; reason : unique_seen_reason }
    (* A child of this value has been used before *)

(* This map is only passed down, never up. *)
type id_env =
  { aliases: Uqid.t list Ident.Map.t;
    (* If several idents refer to the same structure in memory,
       they are mapped to the unique ident x that we saw first.
       In or-patterns we map an ident to a new unique ident for each
       time it occurs in the or-pattern. *)
  }

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
  { last_seen: occurrences Uqid.Map.t;
    (* Match a representing ident to a reason where it was last seen. *)
    children: Uqid.t Projection.Map.t Uqid.Map.t;
    (* The direct children of an identifier (when applying a projection).
       We do not keep global fields (as these are always shared anyway). *)
    parent: Uqid.t Uqid.Map.t;
    (* The parent of a unique ident. We do not keep parents of global fields. *)
  }

(* Matching on a parent does not cause it to be seen automatically. Instead,
   we only mark it as "matched" if we inspect the tags of it (or its children).

   "match x with" will be interpreted with OneParent(uqids of x, Some ..).
   "match e with" will be interpreted with OneParent([Uqid.fresh ..], None).
   "match x, e with" will be interpreted with
     TupleParent([x's uqids, []])

   We have to be careful with or-patterns:

   match x with | Cons(1, y) | y -> y

   Here y aliases x and y is a child of x. When we match on y again, the children
   map could cease to be a tree. To avoid this, we interpret "match y with" by
   taking all Uqids belonging to y as a parent and add children to them individually.
   While this is worst-case exponential, it is unlikely enough that it is
   worth it for code quality. *)
type path_parent = err_id * Occurrence.t

type parent =
  | OneParent of Uqid.t list * path_parent option
  | TupleParent of (Uqid.t list * path_parent option) list

let join_occurrences o1 o2 = match o1, o2 with
  | Many ({children_marked = c1} as o1), Many {children_marked = c2} ->
      Many { o1 with children_marked = c1 || c2 }
  (* We always also join the children and Many always wins *)
  | Many _, _ -> o1
  | _, Many _ -> o2
  | One(s1), One(s2) -> One(Occurrence.Set.union s1 s2)
  | One _, _ -> o1
  | _, One _ -> o2
  | PartlyUsed _, PartlyUsed _ -> o1

let invert_relationship = function
  | Itself -> Itself | Child -> Parent | Parent -> Child

(* Try to make current location shared. If this fails, report this with a previous location. *)
let force_here loc reason relationship occ =
  match Occurrence.force_shared occ with
  | Ok () -> ()
  | Error () ->
      raise (Error(Seen_twice
                      { here = Occurrence.loc occ; here_reason = Occurrence.reason occ;
                        there = loc; there_reason = reason;
                        temporal = ThereBeforeHere; there_is_of_here = relationship }))

(* Try to make previous locations shared. If this fails, report with the current location. *)
let force_previous loc reason relationship occ_set =
  Occurrence.Set.iter (fun occ ->
    match Occurrence.force_shared occ with
    | Ok () -> ()
    | Error () ->
        let relationship = match relationship with
          | Some r -> r
          | None -> invert_relationship (Occurrence.relationship occ) in
        raise (Error(Seen_twice
                        { here = Occurrence.loc occ; here_reason = Occurrence.reason occ;
                          there = loc; there_reason = reason;
                          temporal = HereBeforeThere; there_is_of_here = relationship })))
    occ_set

let rec mark_parents loc reason uid uenv =
  match Uqid.Map.find_opt uid uenv.parent with
  | Some p ->
      let continue, uenv = match Uqid.Map.find_opt p uenv.last_seen with
        | None -> true, { uenv with last_seen = Uqid.Map.add p (PartlyUsed({loc; reason})) uenv.last_seen }
        | Some(PartlyUsed(_)) -> false, uenv (* parents already marked *)
        | Some(Many(_)) -> false, uenv (* parents already marked *)
        | Some(One(occ_set)) ->
            force_previous loc reason (Some Child) occ_set;
            true, { uenv with last_seen = Uqid.Map.add p (Many({loc; reason; relationship = Child; children_marked = false})) uenv.last_seen } in
      if continue then mark_parents loc reason p uenv else uenv
  | _ -> uenv

let rec force_children loc reason uid uenv =
  match Uqid.Map.find_opt uid uenv.children with
  | Some children ->
      Projection.Map.fold (fun _ c uenv ->
          let continue = match Uqid.Map.find_opt c uenv.last_seen with
            | None -> true
            | Some(PartlyUsed(_)) -> true
            | Some(Many({children_marked})) -> not children_marked
            | Some(One(occ_set)) -> force_previous loc reason (Some Parent) occ_set; true in
          let uenv = { uenv with last_seen = Uqid.Map.add c (Many({loc; reason; relationship = Parent; children_marked = true })) uenv.last_seen } in
          if continue then force_children loc reason c uenv else uenv)
        children uenv
  | _ -> uenv

let rec mark_children occ uid uenv =
  match Uqid.Map.find_opt uid uenv.children with
  | Some children ->
      Projection.Map.fold (fun _ c uenv ->
          assert (Uqid.Map.find_opt c uenv.last_seen = None);
          let uenv = { uenv with last_seen = Uqid.Map.add c (One(Occurrence.Set.singleton occ)) uenv.last_seen } in
          mark_children occ c uenv)
        children uenv
  | _ -> uenv

let force_itself ?(need_force_children = true) ?(children_marked = true) ploc preason relationship uid occ uenv =
  let loc = Occurrence.loc occ in
  let reason = Occurrence.reason occ in
  let uenv = { uenv with last_seen = Uqid.Map.add uid (Many({loc;reason;relationship = Itself;children_marked})) uenv.last_seen } in
  force_here ploc preason relationship occ;
  let uenv = if need_force_children then force_children loc reason uid uenv else uenv in
  mark_parents loc reason uid uenv

let mark_seen_ uid occ uenv =
  match Uqid.Map.find_opt uid uenv.last_seen with
  | None ->
      let uenv = { uenv with last_seen = Uqid.Map.add uid (One(Occurrence.Set.singleton occ)) uenv.last_seen } in
      let uenv = mark_children (Occurrence.set_relationship Parent occ) uid uenv in
      mark_parents (Occurrence.loc occ) (Occurrence.reason occ) uid uenv
  | Some(One(occ_set)) ->
      force_previous (Occurrence.loc occ) (Occurrence.reason occ) None occ_set;
      let prev = Occurrence.Set.max_elt occ_set in
      force_itself (Occurrence.loc prev) (Occurrence.reason prev) (Occurrence.relationship prev) uid occ uenv
  | Some(Many({loc;reason;children_marked;relationship})) ->
      force_itself ~need_force_children:(not children_marked) loc reason relationship uid occ uenv
  | Some(PartlyUsed({loc;reason})) ->
      force_itself loc reason Child uid occ uenv
let mark_seen id occ ienv uenv =
  match Ident.Map.find_opt id ienv.aliases with
  | Some aliases -> List.fold_left (fun uenv uid -> mark_seen_ uid occ uenv) uenv aliases
  | None ->
      (* The idents that are not in the alias map are other definitions and indices of loops/comprehensions. *)
      (* Location.alert ~kind:"unreg-var" (Occurrence.loc occ) ("Internal error: " ^ Ident.name id ^ " has not been registered"); *)
      uenv
let mark_seen_all uids occ uenv =
  List.fold_left (fun uenv uid -> mark_seen_ uid occ uenv) uenv uids

let add_child parent proj uenv =
  let uid = Uqid.fresh (Projection.to_string (Uqid.name parent) proj) in
  let parent_last_seen = match Uqid.Map.find_opt parent uenv.last_seen with
    | Some(PartlyUsed _) -> None | o -> o in
  let with_new projs =
    { children = Uqid.Map.add parent (Projection.Map.add proj uid projs) uenv.children;
      parent = Uqid.Map.add uid parent uenv.parent;
      last_seen = Uqid.Map.update uid (function | None -> parent_last_seen | l -> l) uenv.last_seen } in
  match Uqid.Map.find_opt parent uenv.children with
  | None -> uid, with_new Projection.Map.empty
  | Some projs -> match Projection.Map.find_opt proj projs with
    | None -> uid, with_new projs
    | Some old -> old, uenv

let add_child_many parents proj uenv =
  let uenv, ps = List.fold_left_map (fun uenv parent ->
      let uid, uenv = add_child parent proj uenv in uenv, uid)
      uenv parents in
  ps, uenv

let mark_matched parent uenv =
  let mark_matched_one parent occ uenv =
    (* We 'match' on the memory address to disallow matching on already reused memory *)
    let uid, uenv = add_child parent Memory_address uenv in
    match Uqid.Map.find_opt uid uenv.last_seen with
    | None -> uenv
    | Some(One occ_set) ->
        force_previous (Occurrence.loc occ) (Occurrence.reason occ) None occ_set;
        let prev = Occurrence.Set.max_elt occ_set in
        force_itself ~need_force_children:false ~children_marked:false (Occurrence.loc prev) (Occurrence.reason prev) Itself uid occ uenv
    | Some(Many _) -> uenv
    | Some(PartlyUsed _) -> uenv in
  match parent with
  | OneParent(ps, Some (_, occ))->
      List.fold_left (fun uenv p -> mark_matched_one p occ uenv) uenv ps
  | OneParent(_, None) -> uenv (* This is (part of) a global or array field *)
  | TupleParent _ -> uenv (* We have matched on a tuple which we own -- no action necessary *)

let uid_of_ident id =
  Uqid.fresh (Ident.name id)

let add_alias id uids ienv =
  { aliases = Ident.Map.update id (fun muids' -> match muids' with
        | None -> Some uids
        | Some uids' -> Some (uids' @ uids)) ienv.aliases }

let pat_var id parent ienv uenv =
  match parent with
  | OneParent(ps, _) ->
      parent, add_alias id ps ienv, uenv
  | TupleParent ps ->
      let uid = uid_of_ident id in
      let ienv = add_alias id [uid] ienv in
      (* Mark all ps as seen, as we bind the tuple to a variable. *)
      OneParent([uid], None), ienv, List.fold_left (fun uenv (ps, pp_opt) ->
          match pp_opt with
          | None -> uenv
          | Some (err_id, occ) ->
            let occ = Occurrence.fresh (Occurrence.loc occ)
                (Tuple_match_on_aliased_as(err_id, id)) (Occurrence.mode occ) in
            mark_seen_all ps occ uenv) uenv ps

let is_shared_field global_flag = match global_flag with
  | Global -> true
  | Nonlocal -> true
  | Unrestricted -> false

let rec pat_to_map (pat : Typedtree.pattern) parent ienv uenv =
  match pat.pat_desc with
  | Tpat_any -> ienv, uenv
  | Tpat_var(id, _) ->
      let _, ienv, uenv = pat_var id parent ienv uenv in
      ienv, uenv
  | Tpat_alias(pat',id, _) ->
      let parent, ienv, uenv = pat_var id parent ienv uenv in
      pat_to_map pat' parent ienv uenv
  | Tpat_constant(_) -> ienv, mark_matched parent uenv
  | Tpat_tuple(ps) ->
      pat_proj ~handle_tuple:(fun ps' ->
          (* We matched a tuple against a tuple parent and descend into each case *)
          List.fold_left2
            (fun (ienv, uenv) pat' (p, occ) ->
                pat_to_map pat' (OneParent(p, occ)) ienv uenv)
            (ienv, uenv) ps ps'
        ) ~extract_pat:Fun.id ~mk_proj:(fun i _ -> Some (Projection.Tuple_field i)) parent ps ienv uenv
  | Tpat_construct(lbl, _, ps) ->
      pat_proj ~extract_pat:Fun.id ~mk_proj:(fun i _ -> (Some (Projection.Construct_field(Longident.last lbl.txt, i)))) parent ps ienv uenv
  | Tpat_variant(lbl, mpat, _) -> begin
      let uenv = mark_matched parent uenv in
      let pp, (ps, uenv) = match parent with
        | OneParent(ps, pp) -> pp, add_child_many ps (Projection.Variant_field lbl) uenv
        | TupleParent _ -> assert false in
      match mpat with
      | Some pat' -> pat_to_map pat' (OneParent(ps, pp)) ienv uenv
      | None -> ienv, uenv
      end
  | Tpat_record((ps : (_ * _ * _) list), _) ->
      pat_proj ~extract_pat:(fun (_, _, pat) -> pat) ~mk_proj:(fun _ (_, l, _) ->
          if is_shared_field l.lbl_global then None else
            Some (Projection.Record_field(l.lbl_name))) parent ps ienv uenv
  | Tpat_array(ps) ->
      let uenv = mark_matched parent uenv in
      List.fold_left
        (fun (ienv, uenv) pat ->
            pat_to_map pat (OneParent([Uqid.fresh "array_field"], None)) ienv uenv)
        (ienv, uenv) ps
  | Tpat_lazy(pat') -> pat_to_map pat' parent ienv uenv
  | Tpat_or(a, b, _) ->
      let ienv, uenv = pat_to_map a parent ienv uenv in
      pat_to_map b parent ienv uenv
and pat_proj : 'a. ?handle_tuple:_ -> extract_pat:('a -> _) -> mk_proj:(_ -> 'a -> _) -> _ -> 'a list -> _ -> _ -> _ =
  fun ?(handle_tuple = fun _ -> assert false) ~extract_pat ~mk_proj parent ps ienv uenv ->
    match parent with
    | OneParent(parents, pp) ->
        let uenv = mark_matched parent uenv in
        let ienv, uenv, _ =
          List.fold_left
            (fun (ienv, uenv, i) patlike ->
               let pp, (ps, uenv) = match mk_proj i patlike with
                 | None -> None, ([Uqid.fresh "global"], uenv)
                 | Some proj -> pp, add_child_many parents proj uenv in
               let ienv, uenv = pat_to_map (extract_pat patlike) (OneParent(ps, pp)) ienv uenv in
               ienv, uenv, i + 1)
            (ienv, uenv, 0) ps
        in ienv, uenv
    | TupleParent(ps') -> handle_tuple ps'

(* We ignore exceptions in uniqueness analysis. *)
let comp_pat_to_map
      (pat : Typedtree.computation Typedtree.general_pattern) parent ienv uenv =
  match split_pattern pat with
  | Some pat', _ -> pat_to_map pat' parent ienv uenv
  | None, _ -> ienv, uenv

let ident_option_from_path p =
  match p with
  | Path.Pident id -> Some id
  | Path.Pdot _ -> None (* Pdot's can not be unique *)
  | Path.Papply _ -> assert false

let rec check_uniqueness_exp_ exp ienv uenv =
  match exp.exp_desc with
  | Texp_ident(p, _, _, _, mode) -> begin
      match ident_option_from_path p with
      | Some id ->
          let occ = Occurrence.fresh exp.exp_loc
              (Seen_as (Ident id)) mode in
          mark_seen id occ ienv uenv
      | None -> uenv
      end
  | Texp_constant _ -> uenv
  | Texp_let(_, vbs, exp') ->
      let ienv, uenv = check_uniqueness_value_bindings_ vbs ienv uenv in
      check_uniqueness_exp_ exp' ienv uenv
  | Texp_function { param; cases } ->
      check_uniqueness_cases (OneParent([uid_of_ident param], None)) cases ienv uenv
  | Texp_apply(f, xs, _) ->
      let uenv = check_uniqueness_exp_ f ienv uenv in
      List.fold_right (fun (_, arg) uenv -> match arg with
          | Arg e -> check_uniqueness_exp_ e ienv uenv
          | Omitted _ -> uenv) xs uenv
  | Texp_match(e, cs, _) ->
      let parent, uenv = exp_to_parent ~check:true e ienv uenv in
      check_uniqueness_comp_cases parent cs ienv uenv
  | Texp_try(e, cs) ->
      let uenv = check_uniqueness_exp_ e ienv uenv in
      let ps = [Uqid.fresh "try"] in
      check_uniqueness_cases (OneParent(ps, None)) cs ienv uenv
  | Texp_tuple(es) ->
      List.fold_right (fun e uenv -> check_uniqueness_exp_ e ienv uenv) es uenv
  | Texp_construct(_, _, es) ->
      List.fold_right (fun e uenv -> check_uniqueness_exp_ e ienv uenv) es uenv
  | Texp_variant(_, None) -> uenv
  | Texp_variant(_, Some e) -> check_uniqueness_exp_ e ienv uenv
  | Texp_record { fields; extended_expression } -> begin
      let check_fields uenv =
        Array.fold_right (fun f uenv -> match f with
          | _, Kept _ -> uenv
          | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv uenv) fields uenv in
      match extended_expression with
      | None -> check_fields uenv
      | Some (update_kind, exp) ->
        let parent, uenv = path_to_parent ~check:true exp ienv uenv in
        match parent with
        | None -> check_fields uenv
        | Some (ps, (err_id, _), mode) ->
            let uenv = Array.fold_right (fun field uenv -> match field with
              | l, Kept _ ->
                  if is_shared_field l.lbl_global then uenv else
                    let occ = Occurrence.fresh exp.exp_loc (Seen_as (Field(err_id, l.lbl_name))) mode in
                    let ps, uenv = add_child_many ps (Projection.Record_field l.lbl_name) uenv in
                    mark_seen_all ps occ uenv
              | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv uenv) fields uenv
            in match update_kind with
            | In_place ->
                let occ = Occurrence.fresh exp.exp_loc (Seen_as err_id) mode in
                let ps, uenv = add_child_many ps Memory_address uenv in
                mark_seen_all ps occ uenv
            | Create_new -> uenv
      end
  | Texp_field(e, _, l, mode) -> begin
      match (path_to_parent ~check:true e ienv uenv : (Uqid.t list * path_parent * Mode.Uniqueness.t) option * unique_env) with
      | Some (ps, (err_id, _), _), uenv ->
          if is_shared_field l.lbl_global then uenv else
            let occ = Occurrence.fresh exp.exp_loc (Seen_as (Field(err_id, l.lbl_name))) mode in
            let ps, uenv = add_child_many ps (Projection.Record_field l.lbl_name) uenv in
            mark_seen_all ps occ uenv
      | None, uenv -> uenv
    end
  | Texp_setfield(exp', _, _, e) ->
      let _, uenv = path_to_parent ~check:true exp' ienv uenv in
      check_uniqueness_exp_ e ienv uenv
  | Texp_array(es) ->
      List.fold_right (fun e uenv -> check_uniqueness_exp_ e ienv uenv) es uenv
  | Texp_ifthenelse(if', then', else_opt) ->
      let _, uenv = path_to_parent ~check:true if' ienv uenv in
      begin match else_opt with
      | Some else' -> check_uniqueness_parallel [then'; else'] ienv uenv
      | None -> check_uniqueness_exp_ then' ienv uenv
      end
  | Texp_sequence(e, e') ->
      let uenv = check_uniqueness_exp_ e ienv uenv in
      check_uniqueness_exp_ e' ienv uenv
  | Texp_while(e, e') ->
      let uenv = check_uniqueness_exp_ e ienv uenv in
      check_uniqueness_exp_ e' ienv uenv
  | Texp_list_comprehension(e, cs) ->
      let uenv = check_uniqueness_exp_ e ienv uenv in
      check_uniqueness_comprehensions cs ienv uenv
  | Texp_arr_comprehension(e, cs) ->
      let uenv = check_uniqueness_exp_ e ienv uenv in
      check_uniqueness_comprehensions cs ienv uenv
  | Texp_for(_, _, from', to', _, body) ->
      let uenv = check_uniqueness_exp_ from' ienv uenv in
      let uenv = check_uniqueness_exp_ to' ienv uenv in
      check_uniqueness_exp_ body ienv uenv
  | Texp_send(e, _, _, _) ->
      check_uniqueness_exp_ e ienv uenv
  | Texp_new _ -> uenv
  | Texp_instvar _ -> uenv
  | Texp_setinstvar(_, _, _, e) ->
      check_uniqueness_exp_ e ienv uenv
  | Texp_override(_, ls) ->
      List.fold_left (fun uenv (_, _, e) ->
          check_uniqueness_exp_ e ienv uenv
        ) uenv ls
  | Texp_letmodule _ -> uenv (* TODO *)
  | Texp_letexception(_, e) -> check_uniqueness_exp_ e ienv uenv
  | Texp_assert e -> check_uniqueness_exp_ e ienv uenv
  | Texp_lazy e -> check_uniqueness_exp_ e ienv uenv
  | Texp_object _ -> uenv (* TODO *)
  | Texp_pack _ -> uenv (* TODO *)
  | Texp_letop {let_;ands;body} ->
      let uenv = check_uniqueness_binding_op let_ exp ienv uenv in
      let uenv = List.fold_left (fun uenv bop ->
          check_uniqueness_binding_op bop exp ienv uenv) uenv ands in
      check_uniqueness_cases (OneParent ([Uqid.fresh "letop"], None)) [body] ienv uenv
  | Texp_unreachable -> uenv
  | Texp_extension_constructor _ -> uenv
  | Texp_open _ -> uenv (* TODO *)
  | Texp_probe { handler } -> check_uniqueness_exp_ handler ienv uenv
  | Texp_probe_is_enabled _ -> uenv

and path_to_parent : check:bool -> Typedtree.expression -> id_env -> unique_env -> (Uqid.t list * path_parent * Mode.Uniqueness.t) option * unique_env = fun ~check exp ienv uenv ->
  match exp.exp_desc with
  | Texp_ident(p, _, _, _, mode) -> begin
      match ident_option_from_path p with
      | None -> None, uenv
      | Some id ->
          match Ident.Map.find_opt id ienv.aliases with
          | None -> None, uenv
          | Some ps ->
              let err_id = Ident id in
              let occ = Occurrence.fresh exp.exp_loc (Seen_as err_id) mode in
              let uenv = mark_matched (OneParent(ps, Some(err_id, occ))) uenv in
              Some(ps, (err_id, occ), mode), uenv end
  | Texp_field(e, _, l, mode) -> begin
      match path_to_parent ~check e ienv uenv with
      | Some(ps, (err_id, _), _), uenv ->
          let err_id = Field(err_id, l.lbl_name) in
          let occ = Occurrence.fresh exp.exp_loc (Seen_as err_id) mode in
          let ps, uenv = add_child_many ps (Projection.Record_field l.lbl_name) uenv in
          let uenv = mark_matched (OneParent(ps, Some(err_id, occ))) uenv in
          Some(ps, (err_id, occ), mode), uenv
      | _, uenv -> None, uenv end
  (* CR-someday anlorenzen: This could also support let-bindings. *)
  | _ -> None, if check then check_uniqueness_exp_ exp ienv uenv else uenv
and exp_to_parent ~check exp ienv uenv =
  let uid = Uqid.fresh "match" in
  match exp.exp_desc with
  | Texp_tuple(es) ->
      let uenv, ps = List.fold_left_map (fun uenv e ->
          match path_to_parent ~check e ienv uenv with
          | Some(ps, pp, _), uenv -> uenv, (ps, Some pp)
          | None, uenv -> uenv, ([uid], None))
          uenv es in
      TupleParent(ps), uenv
  | _ ->
      match path_to_parent ~check exp ienv uenv with
      | Some (ps, pp, _), uenv -> OneParent(ps, Some pp), uenv
      | None, uenv -> OneParent([uid], None), uenv

and check_uniqueness_value_bindings_ vbs ienv uenv =
  let ienv, uenv = List.fold_left
      (fun (ienv, uenv) vb ->
         let parent, uenv = exp_to_parent ~check:false vb.vb_expr ienv uenv in
         pat_to_map vb.vb_pat parent ienv uenv)
      (ienv, uenv) vbs in
  ienv, List.fold_left (fun uenv vb -> snd (exp_to_parent ~check:true vb.vb_expr ienv uenv)) uenv vbs

and check_uniqueness_parallel es ienv uenv =
  let orig_last_seen = uenv.last_seen in
  let uenv, last_seens = List.fold_left_map (fun uenv e ->
      let uenv = check_uniqueness_exp_ e ienv
        { children = uenv.children; parent = uenv.parent;
          last_seen = orig_last_seen } in
      uenv, uenv.last_seen) uenv es in
  { uenv with last_seen = List.fold_left
                  (Uqid.Map.union (fun _ o1 o2 -> Some (join_occurrences o1 o2)))
                  uenv.last_seen last_seens }

and check_uniqueness_cases_
  : 'a. ('a Typedtree.general_pattern -> parent -> id_env -> unique_env -> id_env * unique_env)
    -> parent -> 'a case list -> id_env -> unique_env -> unique_env =
  fun ptm parent cs ienv uenv ->
  let ienv, uenv = List.fold_left (fun (ienv, uenv) c -> ptm c.c_lhs parent ienv uenv) (ienv, uenv) cs in
  (* We check all guards first, even if this will mark some variables as shared
     unnecessarily. This way we do not have to analyse which guards run when. *)
  let uenv = List.fold_left (fun uenv c -> match c.c_guard with
    | None -> uenv
    | Some g -> check_uniqueness_exp_ g ienv uenv) uenv cs in
  check_uniqueness_parallel (List.map (fun c -> c.c_rhs) cs) ienv uenv

and check_uniqueness_cases parent cs ienv uenv =
  check_uniqueness_cases_ pat_to_map parent cs ienv uenv
and check_uniqueness_comp_cases parent cs ienv uenv =
  check_uniqueness_cases_ comp_pat_to_map parent cs ienv uenv

and check_uniqueness_comprehensions cs ienv uenv =
  List.fold_left (fun uenv c ->
      let uenv = match c.guard with
        | None -> uenv
        | Some e -> check_uniqueness_exp_ e ienv uenv in
      List.fold_left (fun uenv c ->
          match c with
          | From_to(_, _, e1, e2, _) -> check_uniqueness_exp_ e1 ienv (check_uniqueness_exp_ e2 ienv uenv)
          | In(_, e) -> check_uniqueness_exp_ e ienv uenv) uenv c.clauses)
    uenv cs

and check_uniqueness_binding_op bo exp ienv uenv =
  let uenv = match ident_option_from_path bo.bop_op_path with
    | Some id ->
        let occ = Occurrence.fresh exp.exp_loc
            (Seen_as (Ident id)) Mode.Uniqueness.shared in
        mark_seen id occ ienv uenv
    | None -> uenv in
  check_uniqueness_exp_ bo.bop_exp ienv uenv


let check_uniqueness_exp exp =
  let _ = check_uniqueness_exp_ exp
      { aliases = Ident.Map.empty; }
      { last_seen = Uqid.Map.empty;
        children = Uqid.Map.empty;
        parent = Uqid.Map.empty; }
  in ()

let check_uniqueness_value_bindings vbs =
  let _ = check_uniqueness_value_bindings_ vbs
      { aliases = Ident.Map.empty; }
      { last_seen = Uqid.Map.empty;
        children = Uqid.Map.empty;
        parent = Uqid.Map.empty; }
  in ()

let print_relationship = function
  | Child -> "a child" | Parent -> "a parent" | Itself -> "an alias"

let rec print_err_id = function
  | Ident id -> Ident.name id
  | Field(id, s) -> Projection.to_string (print_err_id id) (Record_field s)

let report_error = function
  | Seen_twice err ->
      let temporal = match err.temporal with
        | HereBeforeThere -> "It will be used again at:"
        | ThereBeforeHere -> "It was used previously at:" in
      let there_explanation id = match err.there_reason with
        | Seen_as eid' ->
            let id' = print_err_id eid' in
            if id = id' then Format.dprintf "" else
              Format.dprintf
                "%s was used because %s is %s of %s." id id' (print_relationship err.there_is_of_here) id
        | Tuple_match_on_aliased_as(eid', alias') ->
            let id' = print_err_id eid' in
            if id = id'
            then Format.dprintf
                "%s was used because %s refers to a tuple containing it."
                id (Ident.name alias')
            else Format.dprintf
                "%s was used because %s refers to a tuple@ \
                 containing %s, which is %s of %s."
                id (Ident.name alias') id' (print_relationship err.there_is_of_here) id in
      match err.here_reason with
      | Seen_as eid ->
        let id = print_err_id eid in
        Location.errorf ~loc:err.here
          ~sub:[Location.msg ~loc:err.there "@[%t @]" (there_explanation id)]
          "@[%s is used uniquely here so cannot be used twice. %s@]" id temporal
      | Tuple_match_on_aliased_as(eid, alias) ->
        let id = print_err_id eid in
        Location.errorf ~loc:err.here
          ~sub:[Location.msg ~loc:err.there "@[%t @]" (there_explanation id)]
          "@[%s is used uniquely here so cannot be used twice (%s refers to a tuple containing it). %s@]" id (Ident.name alias) temporal

let report_error err =
  Printtyp.wrap_printing_env ~error:true Env.empty
    (fun () -> report_error err)

let () =
  Location.register_error_of_exn
    (function
      | Error (err) ->
          Some (report_error err)
      | _ ->
          None
    )
