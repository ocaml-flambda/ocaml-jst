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

module Uniqueness = Mode.Uniqueness
module Linearity = Mode.Linearity

(* New names to avoid polluting the Ident namespace.
   These new names usually refer to "memory locations" rather than source identifiers.
   Example: match x with | A y ->
              match x with | A z ->  ... y ... z ...

   Here, we will use a single Root_id to refer to 'x.A.1'. The Idents y and z
   are then mapped to the Root_id 'x.A.1'. We do not use these names for error
   reporting as 'x.A.1' is a worse name than 'y'. *)

module Occurrence = struct
  (* The occurrence of a potentially unique ident in the expression. *)
  type reason =
  | DirectUse  (* it is used directly *)
  | MatchTupleWithVar of Location.t
    (* When matching on a tuple, we do not construct a tuple and match on it,
        but rather match on the individual elements of the tuple -- this preserves
        their uniqueness. But in a pattern an alias to the tuple could be created,
        in which case we have to construct the tuple and retroactively mark the
        elements as seen. *)
    (* location points to the Tpat_var or Tpat_alias *)

  type t = {
    loc : Location.t;
    reason : reason
  }

end

module SharedUnique = struct
  (* this module is about the distinction
     between unique and shared *)

  (* which axis cannot be forced? *)
  type error = [`Uniqueness | `Linearity ]

  exception CannotForce of
  {
    (* the occurrence that's failing forcing *)
    here : Occurrence.t;
    (* the other occurrence that triggers the forcind *)
    there : Occurrence.t;
    (* CR zqian:
    describe the relation between here and there,
    including the full path from the ancestor to the descendant as a list of
    projections *)
    (* which axis failed to force? *)
    error : error
  }

  type maybe_unique = {
    modes : Mode.Uniqueness.t * Mode.Linearity.t;
    occ : Occurrence.t
  }
  type t =
    | Shared of Occurrence.t
    | MaybeUnique of maybe_unique list

  let force t there =
    match t with
    | Shared _ -> t
    | MaybeUnique l ->
    let force_one {modes = (uni,lin); occ} =
      (match Mode.Linearity.submode lin (Mode.Linearity.many) with
      | Ok () -> ()
      | Error () -> raise (CannotForce {here = occ; there; error = `Linearity})
      );
      match Mode.Uniqueness.submode (Mode.Uniqueness.shared) uni with
      | Ok () -> ()
      | Error () -> raise (CannotForce {here = occ; there; error = `Uniqueness})
    in
      List.iter force_one l;
      let occ = (List.hd l).occ in
      Shared occ

  let par t0 t1 =
    match t0, t1 with
    | Shared _, t | t, Shared _ -> t
    | MaybeUnique l0, MaybeUnique l1 -> MaybeUnique (l0 @ l1)

  let extract_occurrence = function
  | Shared occ -> occ
  | MaybeUnique l -> (List.hd l).occ

  let seq m0 m1 =
    let m0 = force m0 (extract_occurrence m1) in
    let m1 = force m1 (extract_occurrence m0) in
    m1

end

module Usage = struct
  (* We have Unused (top) > Borrowed > Shared > Unique > Error (bot).

      Unused and Borrowed are infered from syntax;
      Shared and Unique are to be inferred by the analysis. We use the existing
      infrastructure of mode var to represent that.
      Error is represented by just exception
      the Set of Meet must be non-empty

  *)
  type t = Unused | Borrowed of Occurrence.t | SharedUnique of SharedUnique.t

  let _to_string = function
  | Unused -> "unused"
  | Borrowed _-> "borrow"
  | SharedUnique _ -> "maybe_unique"

  let _print ppf t = Format.fprintf ppf "%s" (_to_string t)

  let par m0 m1 = match m0, m1 with
  | Unused, m | m, Unused -> m
  | Borrowed _, m | m, Borrowed _ -> m
  | SharedUnique m0, SharedUnique m1 -> SharedUnique (SharedUnique.par m0 m1)

  let seq m0 m1 =
    match m0, m1 with
    | Unused, m | m, Unused -> m
    | Borrowed _, m -> m
    | SharedUnique m, Borrowed there ->
      SharedUnique (SharedUnique.force m there)
    | SharedUnique m0, SharedUnique m1 ->
      SharedUnique (SharedUnique.seq m0 m1)
end

module UsageTree = struct
  (* Projections from parent to child in match statement. *)
  module Projection = struct
    module T = struct
      type t =
        | Tuple_field of int
        | Record_field of string
        | Construct_field of string * int
        | Variant_field of label
        | Memory_address

      let _print ppf = function
      | Tuple_field i -> Format.fprintf ppf ".%i" i
      | Record_field s -> Format.fprintf ppf ".%s" s
      | Construct_field (s, i) -> Format.fprintf ppf "|%s.%i" s i
      | Variant_field l -> Format.fprintf ppf "|%s" l
      | Memory_address -> Format.fprintf ppf ".*"

      let to_string (t:t) = Format.asprintf "%a" _print t

      let compare t1 t2 =
        String.compare (to_string t1) (to_string t2)
    end
    include T
    module Map = Map.Make(T)

  end

  (* the definition of trees;
    only record direct use; i.e. `x.y` does not register as using `x` or `x.y.z`.
    Implicitly of course, using `x.y` implies using all descendants of `x.y`.

    Each node records the par on all possible path. As a result, trees such as
    `S -> U` is valid, even though it would be invalid if it was the result of a
    single path: using a parent shared and a child uniquely is obviously bad.
    Howerver, it might be the result of "par"ing multiple path: `S` par `N -> U`,
    which is valid.
    *)

  (* INVARIANT: children always higher than parent. *)
  (* Leaf implicitly have children, all of which have the same mode as the leaf *)
  type t =
    { children : t Projection.Map.t;
      usage : Usage.t;
    }

  let rec _print_children ppf children =
    Projection.Map.iter (fun proj child ->
        Format.fprintf ppf "%a = %a,"
        Projection._print proj
        _print  child
      ) children

  and _print ppf t =
      Format.fprintf ppf
      "%a {%a}" Usage._print t.usage
      _print_children t.children

  module Path = struct
    type t = Projection.t list
    let child (p : t) (a : Projection.t) : t= p @ [a]

    let root : t = []
  end

  let leaf usage = {usage; children = Projection.Map.empty}
  let empty = leaf Usage.Unused

  (* lift par and seq to trees *)

  (* invariant preserved because Usage.par is monotone *)
  let rec par t0 t1 =
    {
      usage = Usage.par t0.usage t1.usage;
      children = Projection.Map.merge
      (fun _proj c0 c1 ->
        let c0 = Option.value c0 ~default:t0 in
        let c1 = Option.value c1 ~default:t1 in
        Some (par c0 c1))
      t0.children t1.children
    }


  (* m0 is the lowest mode among the ancestors of t0
  similar for m1;
  This is needed to find conflict between parent in one tree
  and child in the other tree. *)
  (* CR zqian: _proj is ignored; of course we should use it for
  better error info *)
  let rec seq t0 t1 =
    (* Format.eprintf "UsageTree.seq %a and %a \n" _print t0 _print t1; *)
    {
      usage = Usage.seq t0.usage t1.usage;
      children = Projection.Map.merge (fun _proj c0 c1 ->
        (* CR zqian: leaf is allocation here; surely we can optimize away;
          solution: observe that children is very often empty.  Have seq takes
          usage and children, instead of {usage;children}. children can be None.
            *)
        let c0 = Option.value c0 ~default:(leaf t0.usage) in
        let c1 = Option.value c1 ~default:(leaf t1.usage) in
        (* Format.eprintf "UsageTree: diving into %a\n" Projection._print _proj; *)
        Some (seq c0 c1)
      ) t0.children t1.children
    }

  let rec singleton path leaf =
    match path with
    | [] -> {
      usage = leaf;
      children = Projection.Map.empty
    }
    | proj :: path -> {
      usage = Unused;
      children = Projection.Map.singleton proj (singleton path leaf)
    }
end

module UsageForest = struct
  module Root_id = struct
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

    let fresh_of_ident ident = fresh (Ident.name ident)

    let name t1 = t1.name

    let _print ppf t = Format.fprintf ppf "%s" (name t)
  end
  (* maps rootid to trees; contains only the roots *)
  type t = UsageTree.t Root_id.Map.t

  let _print ppf t =
    Root_id.Map.iter (fun rootid tree ->
      Format.fprintf ppf "%a = %a, "
      Root_id._print rootid
      UsageTree._print tree
      ) t

  module Path = struct

    type t = Root_id.t * UsageTree.Path.t

    let child ((rootid, path):t) proj : t = (rootid, UsageTree.Path.child path
    proj)

    let child_of_many paths proj = List.map (fun path -> child path proj) paths

    let fresh_root name : t = (Root_id.fresh name, UsageTree.Path.root)

    let fresh_root_of_id id = (Root_id.fresh_of_ident id, UsageTree.Path.root)
  end

  let empty = Root_id.Map.empty

  let par : t -> t -> t = fun t0 t1 ->
    Root_id.Map.merge (fun _rootid t0 t1 ->
      let t0 = Option.value t0 ~default:UsageTree.empty in
      let t1 = Option.value t1 ~default:UsageTree.empty in
      Some (UsageTree.par t0 t1)) t0 t1

  let seq : t -> t -> t = fun t0 t1 ->
    Root_id.Map.merge (fun _rootid t0 t1 ->
      let t0 = Option.value t0 ~default:UsageTree.empty in
      let t1 = Option.value t1 ~default:UsageTree.empty in
      Some (UsageTree.seq t0 t1)) t0 t1

  let pars l = List.fold_left par empty l

  let seqs l = List.fold_left seq empty l

  let singleton (rootid, path) leaf =
    Root_id.Map.singleton rootid (UsageTree.singleton path leaf)

end

module Uenv = UsageForest
(* Matching on a parent does not cause it to be seen automatically. Instead,
   we only mark it as "matched" if we inspect the tags of it (or its children).

   "match x with" will be interpreted with MatchSingle(rootids of x, Some ..).
   "match e with" will be interpreted with MatchSingle([Root_id.fresh ..], None).
   "match x, e with" will be interpreted with
     MatchTuple([x's rootids, []])

   We have to be careful with or-patterns:

   match x with | Cons(1, y) | y -> y

   Here y aliases x and y is a child of x. When we match on y again, the children
   map could cease to be a tree. To avoid this, we interpret "match y with" by
   taking all Root_ids belonging to y as a parent and add children to them individually.
   While this is worst-case exponential, it is unlikely enough that it is
   worth it for code quality. *)

module Ienv = struct
(* idents are mapped to multiple possible uq, each represented by
the root uq and a path, instead of directly ponting to the uq. *)

    (* If several idents refer to the same structure in memory,
       they are mapped to the unique ident x that we saw first.
       In or-patterns we map an ident to a new unique ident for each
       time it occurs in the or-pattern. *)

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
   When we see y, we mark only y as seen. When we see z, we mark y as seen.
   When we see x, we mark x and y as seen. If y was already marked,
   it must have been seen already and we fail. *)
  type t = UsageForest.Path.t list Ident.Map.t

  (* used for or patterns. This operation is commutative  *)
  let par ienv0 ienv1 =
    Ident.Map.merge (fun _id locs0 locs1 ->
      match locs0, locs1 with
      | None, None -> assert false
      | None, Some t | Some t, None -> Some t
      | Some locs0, Some locs1 -> Some (locs0 @ locs1)
      ) ienv0 ienv1

  (* ienv0 is the old env; ienv1 is probably the new bindings to be added after
  pattern matching. ienv1 simply overwrite ienv0 *)
  let seq ienv0 ienv1 =
    Ident.Map.merge (fun _id locs0 locs1 ->
      match locs0, locs1 with
      | None, None -> assert false
      | Some t, None -> Some t
      | _, Some t -> Some t
    ) ienv0 ienv1

  let empty = Ident.Map.empty

  let seqs ienvs = List.fold_left seq empty ienvs

  let _pars ienvs = List.fold_left par empty ienvs

  let singleton id locs =
    Ident.Map.singleton id locs
end

(* contains two things.
First is the value's all possible paths.
Second is (if it was a variable) its modes and occurrence; this is needed if
turns out we need to use or borrow the value (instead of just creating alias)
*)
type single_value_to_match = Uenv.Path.t list * SharedUnique.maybe_unique option

(* represent a right hand side value *)
type value_to_match =
  (* first is the special case of tuples; we treat it specially so matching
  tuples against tuples merely create alias instead of uses *)
  (* forgive me for making it recursive: just much simpler *)
  | MatchTuple of single_value_to_match list
  (* all the other cases are simple. A value is represented as the list of all
  possible memory locations. If it is in the form of x or x.y, we also record
  that occurence *)
  | MatchSingle of single_value_to_match

let mark_borrow_one path occ =
  (* borrow the memory address of the parent *)
  Uenv.singleton (Uenv.Path.child path UsageTree.Projection.Memory_address)
  (Borrowed occ)

let mark_borrow paths occ =
  Uenv.pars (List.map (fun path -> mark_borrow_one path occ) paths)

let mark_borrow_value = function
  | MatchSingle (_, None) -> Uenv.empty
  | MatchSingle (paths, Some maybe_unique) -> mark_borrow paths
  (maybe_unique.SharedUnique.occ)
  | MatchTuple _ -> Uenv.empty

let mark_use_one path maybe_unique =
  Uenv.singleton path (SharedUnique (MaybeUnique [maybe_unique]))

let mark_use_all paths maybe_unique =
  Uenv.pars (List.map (fun path -> mark_use_one path maybe_unique) paths)

(* takes identier and occurrence *)
let mark_use id maybe_unique ienv =
  match Ident.Map.find_opt id ienv with
  | Some paths -> mark_use_all paths maybe_unique
  | None -> Uenv.empty

(* returns:
   the updated value.
   the new introduced binding.
   usage during the process
  *)
let pattern_match_var ~loc id value =
  match value with
  | MatchSingle (paths, _) ->
      value, Ienv.singleton id paths, UsageForest.empty
  | MatchTuple ps ->
      let path = Uenv.Path.fresh_root_of_id id in
      let ienv = Ienv.singleton id [path] in
      (* Mark all ps as seen, as we bind the tuple to a variable. *)
      (* Can we make it aliases instead of used? Hard to do if we want
     to preserve the tree-ness *)
      MatchSingle ([path], None), ienv,
      Uenv.pars (List.map (fun (ps, pp_opt) ->
          match pp_opt with
          | None -> Uenv.empty
          | Some maybe_unique ->
              let occ = {maybe_unique.SharedUnique.occ with reason = MatchTupleWithVar loc}
              in
              let maybe_unique = {maybe_unique with SharedUnique.occ} in
              mark_use_all ps maybe_unique) ps)

let is_shared_field global_flag = match global_flag with
  | Global -> true
  | Nonlocal -> true
  | Unrestricted -> false

(*
handling pattern match of value against pat, returns ienv and uenv.
ienv is the new bindings introduced;
uenv is the usage caused by the pattern matching *)
let rec pattern_match pat value =
  match pat.pat_desc with
  | Tpat_any -> Ienv.empty, UsageForest.empty
  | Tpat_var(id, _, _) ->
      let _, ienv, uenv = pattern_match_var ~loc:(pat.pat_loc) id value in
      ienv, uenv
  | Tpat_alias(pat',id, _, _) ->
      let value, ienv0, uenv0 = pattern_match_var ~loc:(pat.pat_loc) id value in
      let ienv1, uenv1 = pattern_match pat' value in
      Ienv.seq ienv0 ienv1, UsageForest.seq uenv0 uenv1
  | Tpat_constant(_) -> Ienv.empty, mark_borrow_value value
  | Tpat_tuple(pats) ->
      pat_proj ~handle_tuple:(fun values ->
          (* We matched a tuple against a tuple parent and descend into each
          case *)
          let ienvs, uenvs = List.split (List.map2
            (fun pat' (p, occ) ->
              pattern_match pat' (MatchSingle(p, occ))) pats values)
          in
          Ienv.seqs ienvs, UsageForest.seqs uenvs
        ) ~extract_pat:Fun.id ~mk_proj:(fun i _ -> Some (UsageTree.Projection.Tuple_field
        i)) value pats
  | Tpat_construct(lbl, _, pats,_) ->
      pat_proj ~extract_pat:Fun.id ~mk_proj:(fun i _ -> (Some
      (UsageTree.Projection.Construct_field(Longident.last lbl.txt, i)))) value pats
  | Tpat_variant(lbl, mpat, _) -> begin
      let uenv = mark_borrow_value value in
      let pp, ps = match value with
        | MatchSingle(ps, pp) -> pp,
          Uenv.Path.child_of_many ps (UsageTree.Projection.Variant_field lbl)
        | MatchTuple _ -> assert false
      in
      let ienv, uenv' = match mpat with
      | Some pat' -> pattern_match pat' (MatchSingle(ps, pp))
      | None -> Ienv.empty, UsageForest.empty
      in
      ienv, UsageForest.seq uenv uenv'
    end
  | Tpat_record((pats : (_ * _ * _) list), _) ->
      pat_proj ~extract_pat:(fun (_, _, pat) -> pat) ~mk_proj:(fun _ (_, l, _) ->
          if is_shared_field l.lbl_global then None else
            Some (UsageTree.Projection.Record_field(l.lbl_name))) value pats
  | Tpat_array(_, pats) ->
      let uenv = mark_borrow_value value in
      let ienvs, uenvs =
        List.split (List.map
          (fun pat ->
            pattern_match pat (MatchSingle([Uenv.Path.fresh_root "array_field"],
            None))) pats)
      in
      Ienv.seqs ienvs, UsageForest.seqs (uenv :: uenvs)
  | Tpat_lazy(pat') -> pattern_match pat' value
  | Tpat_or(a, b, _) ->
      let ienv0, uenv0 = pattern_match a value in
      let ienv1, uenv1 = pattern_match b value in
      (* note that we use Ienv.par *)
      Ienv.par ienv0 ienv1, UsageForest.seq uenv0 uenv1

and pat_proj : 'a. ?handle_tuple:_ -> extract_pat:('a -> _) -> mk_proj:(_ -> 'a -> _) -> _ -> 'a list -> _  =
  fun ?(handle_tuple = fun _ -> assert false) ~extract_pat ~mk_proj value pats ->
    match value with
    | MatchSingle(values, pp) ->

        let uenv = mark_borrow_value value in
        let ienvs, uenvs = List.split(
          List.mapi
            (fun i patlike ->
                let pp, ps = match mk_proj i patlike with
                 | None -> None, [Uenv.Path.fresh_root "global"]
                 | Some proj -> pp, UsageForest.Path.child_of_many values proj
                in
                 pattern_match (extract_pat patlike) (MatchSingle(ps, pp))
            ) pats)
        in
        Ienv.seqs ienvs, UsageForest.seqs (uenv :: uenvs)
    | MatchTuple(values) -> handle_tuple values

(* We ignore exceptions in uniqueness analysis. *)
let comp_pattern_match
      pat value =
  match split_pattern pat with
  | Some pat', _ -> pattern_match pat' value
  | None, _ -> Ienv.empty, Uenv.empty

let ident_option_from_path p =
  match p with
  | Path.Pident id -> Some id
  | Path.Pdot _ -> None (* TODO: what does this line mean? *)
  | Path.Papply _ -> assert false

(* returns uenv, which is the usage of the expression *)
let rec check_uniqueness_exp_ exp (ienv : Ienv.t) : Uenv.t =
  match exp.exp_desc with
  | Texp_ident(p, _, _, _, use) -> begin
      match ident_option_from_path p with
      | Some id ->
          let maybe_unique = {SharedUnique.modes = use;
            occ = {
              loc = exp.exp_loc;
              reason = DirectUse
              }
          } in
          mark_use id maybe_unique ienv
      | _ -> UsageForest.empty
      end
  | Texp_constant _ -> Uenv.empty
  | Texp_let(_, vbs, exp') ->
      let ienv', uenv = check_uniqueness_value_bindings_ vbs ienv in
      let uenv' = check_uniqueness_exp_ exp' (Ienv.seq ienv ienv') in
      Uenv.seq uenv uenv'
  | Texp_function { param; cases } ->
      (* `param` is only a hint not a binder;
      actual binding done in cases by Tpat_var and Tpat_alias *)
      let value = MatchSingle([Uenv.Path.fresh_root_of_id param], None) in
      let uenv = check_uniqueness_cases value cases ienv in
      (* Format.eprintf "fun %s -> %a end \n" (Ident.name param) Uenv._print uenv; *)
      uenv
  | Texp_apply(f, xs, _, _) ->
      let uenv = check_uniqueness_exp_ f ienv in
      let uenvs = List.map (fun (_, arg) ->
        match arg with
        | Arg e -> check_uniqueness_exp_ e ienv
        | Omitted _ -> Uenv.empty
        ) xs
      in (
        (* Format.eprintf "apply %a (%a)\n" Uenv._print uenv
        (Format.pp_print_list Uenv._print) uenvs
        ; *)
      Uenv.seqs (uenv :: uenvs)
      )
  | Texp_match(e, cs, _) ->
      let value, uenv = init_value_to_match e ienv in
      let uenv' = check_uniqueness_comp_cases value cs ienv in (
      (* Format.eprintf "match %a -> %a\n" Uenv._print uenv Uenv._print uenv'; *)
      Uenv.seq uenv uenv'
      )
  | Texp_try(e, cs) ->
      let uenv = check_uniqueness_exp_ e ienv in
      let ps = [Uenv.Path.fresh_root "try"] in
      let uenv' = check_uniqueness_cases (MatchSingle(ps, None)) cs ienv in
      (* we don't know how much of e will be run; safe to assume all of them *)
      Uenv.seq uenv uenv'
  | Texp_tuple(es, _) ->
      Uenv.seqs (List.map (fun e -> check_uniqueness_exp_ e ienv) es)
  | Texp_construct(_, _, es, _) ->
      Uenv.seqs (List.map (fun e -> check_uniqueness_exp_ e ienv) es)
  | Texp_variant(_, None) -> Uenv.empty
  | Texp_variant(_, Some (e, _)) -> check_uniqueness_exp_ e ienv
  | Texp_record { fields; extended_expression } -> begin
      let check_fields =
        Uenv.seqs (Array.to_list (Array.map (fun field -> match field with
          | _, Kept _ -> Uenv.empty
          | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv ) fields))
      in
      match extended_expression with
      | None -> check_fields
      | Some (update_kind, exp) ->
        let value, uenv = maybe_lvalue exp ienv in
        match value with
        | None -> check_fields  (* {exp with ...}; don't know anything about exp
        so nothing we can do here*)
        | Some (ps, maybe_unique) -> (* {x with ...} *)
            let uenv = Array.fold_right (fun field uenv -> match field with
              | l, Kept _ ->
                  if is_shared_field l.lbl_global then uenv else
                    let maybe_unique = {
                      maybe_unique with
                      SharedUnique.occ = {loc = exp.exp_loc;
                                          reason = DirectUse
                                          }
                      }  in
                    let ps = Uenv.Path.child_of_many ps (UsageTree.Projection.Record_field l.lbl_name) in
                    mark_use_all ps maybe_unique
              | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv) fields uenv
            in match update_kind with
            | In_place ->
                let maybe_unique = {
                  maybe_unique with
                  SharedUnique.occ =
                  {loc = exp.exp_loc;
                  reason = DirectUse}
                  } in
                let ps = Uenv.Path.child_of_many ps Memory_address in
                mark_use_all ps maybe_unique
            | Create_new -> uenv
      end
  | Texp_field(e, _, l, modes, _) -> begin
      match maybe_lvalue e ienv with
      | Some (ps, _), uenv ->
          if is_shared_field l.lbl_global then uenv else
            let occ = {Occurrence.loc = exp.exp_loc; reason = Occurrence.DirectUse} in
            let maybe_unique = { SharedUnique.occ; modes} in
            let ps = Uenv.Path.child_of_many ps (UsageTree.Projection.Record_field l.lbl_name) in
            mark_use_all ps maybe_unique
      | None, uenv -> uenv
    end
  | Texp_setfield(exp', _, _, _, e) ->
      let _, uenv0 = maybe_lvalue exp' ienv in
      let uenv1 = check_uniqueness_exp_ e ienv in
      Uenv.seq uenv0 uenv1
  | Texp_array(_, es, _) ->
      Uenv.seqs (List.map (fun e -> check_uniqueness_exp_ e ienv ) es)
  | Texp_ifthenelse(if', then', else_opt) ->
      let _, uenv0 = maybe_lvalue if' ienv in
      let uenv1 = match else_opt with
      | Some else' -> Uenv.par
        (check_uniqueness_exp_ then' ienv)
        (check_uniqueness_exp_ else' ienv)
      | None -> check_uniqueness_exp_ then' ienv
      in (
      (* Format.eprintf "if %a thenelse %a\n" Uenv._print uenv0 Uenv._print uenv1; *)
      let uenv = Uenv.seq uenv0 uenv1 in
      (* Format.eprintf "= %a \n" Uenv._print uenv; *)
      uenv
      )
  | Texp_sequence(e, e') ->
      let uenv0 = check_uniqueness_exp_ e ienv in
      let uenv1 = check_uniqueness_exp_ e' ienv in
      Uenv.seq uenv0 uenv1
  | Texp_while{wh_cond;wh_body;_} ->
      let uenv0 = check_uniqueness_exp_ wh_cond ienv in
      let uenv1 = check_uniqueness_exp_ wh_body ienv in
      Uenv.seq uenv0 uenv1
  | Texp_list_comprehension{comp_body; comp_clauses} ->
      let uenv0 = check_uniqueness_exp_ comp_body ienv in
      let uenv1 = check_uniqueness_comprehensions comp_clauses ienv in
      Uenv.seq uenv0 uenv1
  | Texp_array_comprehension(_, {comp_body; comp_clauses}) ->
      let uenv0 = check_uniqueness_exp_ comp_body ienv in
      let uenv1 = check_uniqueness_comprehensions comp_clauses ienv in
      Uenv.seq uenv0 uenv1
  | Texp_for{for_from;for_to;for_body;_} ->
      let uenv0 = check_uniqueness_exp_ for_from ienv in
      let uenv1 = check_uniqueness_exp_ for_to ienv in
      let uenv2 = check_uniqueness_exp_ for_body ienv in
      Uenv.seqs [uenv0; uenv1; uenv2]
  | Texp_send(e, _, _, _) ->
      check_uniqueness_exp_ e ienv
  | Texp_new _ -> Uenv.empty
  | Texp_instvar _ -> Uenv.empty
  | Texp_setinstvar(_, _, _, e) ->
      check_uniqueness_exp_ e ienv
  | Texp_override(_, ls) ->
      Uenv.seqs (List.map (fun (_, _, e) ->
          check_uniqueness_exp_ e ienv
        ) ls)
  | Texp_letmodule _ -> Uenv.empty (* TODO *)
  | Texp_letexception(_, e) -> check_uniqueness_exp_ e ienv
  | Texp_assert e -> check_uniqueness_exp_ e ienv
  | Texp_lazy e -> check_uniqueness_exp_ e ienv
  | Texp_object _ -> Uenv.empty (* TODO *)
  | Texp_pack _ -> Uenv.empty (* TODO *)
  | Texp_letop {let_;ands;body} ->
      let uenv0 = check_uniqueness_binding_op let_ exp ienv in
      let uenvs1 = List.map (fun bop ->
          check_uniqueness_binding_op bop exp ienv) ands in
      let uenv2 =
      check_uniqueness_cases (MatchSingle ([Uenv.Path.fresh_root "letop"], None)) [body]
      ienv
      in
      Uenv.seqs (uenv0 :: uenvs1 @ [uenv2])
  | Texp_unreachable -> Uenv.empty
  | Texp_extension_constructor _ -> Uenv.empty
  | Texp_open _ -> Uenv.empty (* TODO *)
  | Texp_probe { handler } -> check_uniqueness_exp_ handler ienv
  | Texp_probe_is_enabled _ -> Uenv.empty

(* looks at exp and see if it can be treated as simple value.
currently only texp_ident and texp_field (and recursively so) are treated so.
return paths and use. paths is the list of possible memory locations.
returns None if exp is not simple value
*)
and maybe_lvalue exp ienv =
  match exp.exp_desc with
  | Texp_ident(p, _, _, _, modes) -> begin
      match ident_option_from_path p with
      | None -> None, Uenv.empty
      | Some id ->
        (* TODO: why not in ienv? *)
          match Ident.Map.find_opt id ienv with
          | None -> None, Uenv.empty
          | Some ps ->
              let occ = {Occurrence.loc = exp.exp_loc; reason = DirectUse} in
              let maybe_unique = {SharedUnique.occ; modes} in
              Some(ps, maybe_unique), Uenv.empty
      end
  | Texp_field(e, _, l, modes, _) -> begin
      match maybe_lvalue e ienv with
      | (Some(paths, maybe_unique), uenv) ->
          (* accessing the field meaning borrowing the parent record .
          note that the field itself is not borrowed or used *)
          let uenv' = mark_borrow paths maybe_unique.SharedUnique.occ in
          let occ = {Occurrence.loc = exp.exp_loc; reason = DirectUse} in
          let maybe_unique = {SharedUnique.occ; modes} in
          let paths' = Uenv.Path.child_of_many paths (UsageTree.Projection.Record_field l.lbl_name) in
          Some(paths', maybe_unique), Uenv.seq uenv uenv'
      | (None, uenv) -> None, uenv
    end
  (* CR-someday anlorenzen: This could also support let-bindings. *)
  | _ -> None, check_uniqueness_exp_ exp ienv

and init_single_value_to_match exp ienv =
  match maybe_lvalue exp ienv with
  | Some (ps, pp), uenv -> (ps, Some pp), uenv
  | None, uenv -> ([Uenv.Path.fresh_root "match"], None), uenv

(* take typed expression, do some parsing and give init_value_to_match *)
and init_value_to_match exp ienv =
  match exp.exp_desc with
  | Texp_tuple(es, _) ->
      let ps, uenvs =
      List.split (List.map (fun e ->
        init_single_value_to_match e ienv) es)
      in
      MatchTuple(ps), Uenv.seqs uenvs
  | _ ->
    let s, uenv = init_single_value_to_match exp ienv
    in
    MatchSingle s, uenv

(* returns ienv and uenv
ienv is the new bindings introduced;
uenv is the usage forest caused by the binding
*)
and check_uniqueness_value_bindings_ vbs ienv =
(* we imitate how data are accessed at runtime *)
  let ienvs, uenvs = List.split (List.map
      (fun vb ->
         let value, uenv = init_value_to_match vb.vb_expr ienv in
         let ienv, uenv' = pattern_match vb.vb_pat value in
         ienv, Uenv.seq uenv uenv'
         )
      vbs)
  in
  Ienv.seqs ienvs, Uenv.seqs uenvs


(* type signature needed because high-ranked *)
and check_uniqueness_cases_
: 'a. ('a Typedtree.general_pattern -> value_to_match -> Ienv.t * Uenv.t)
-> value_to_match -> 'a case list ->  Ienv.t -> Uenv.t =
fun ptm value cases ienv ->
  (* In the following we imitate how data are accessed at runtime for cases *)
  (* we first evaluate all LHS including all the guards, _sequentially_ *)
  let ienvs, uenvs0 = List.split (List.map (fun case ->
    let ienv', uenv = ptm case.c_lhs value in
    let uenv' = match case.c_guard with
    | None -> UsageForest.empty
    | Some g -> check_uniqueness_exp_ g (Ienv.seq ienv ienv')
    in
    ienv', UsageForest.seq uenv uenv'
    ) cases)
  in
  (* we then evaluate all RHS, in _parallel_ *)
  let uenvs1 = List.map2 (fun ienv' case ->
    check_uniqueness_exp_ case.c_rhs (Ienv.seq ienv ienv')
    ) ienvs cases
  in
  UsageForest.seq (UsageForest.seqs uenvs0) (UsageForest.pars uenvs1)

and check_uniqueness_cases value cases ienv =
  check_uniqueness_cases_ pattern_match value cases ienv
and check_uniqueness_comp_cases value cases ienv =
  check_uniqueness_cases_ comp_pattern_match value cases ienv

and check_uniqueness_comprehensions cs ienv =
  Uenv.seqs (List.map (fun c ->
      match c with
        | Texp_comp_when e -> check_uniqueness_exp_ e ienv
        | Texp_comp_for cbs ->
          Uenv.seqs (List.map (fun cb ->
            match cb.comp_cb_iterator with
            | Texp_comp_range{start; stop; _} ->
              let uenv0 = check_uniqueness_exp_ start ienv in
              let uenv1 = check_uniqueness_exp_ stop ienv in
              Uenv.seq uenv0 uenv1
            | Texp_comp_in{sequence; _} -> check_uniqueness_exp_ sequence ienv
            ) cbs)
  ) cs)

and check_uniqueness_binding_op bo exp ienv =
  let uenv0 = match ident_option_from_path bo.bop_op_path with
    | Some id ->
        let occ = {Occurrence.loc = exp.exp_loc; reason = DirectUse} in
        let maybe_unique = {SharedUnique.occ; modes = (
          Uniqueness.shared,
          Linearity.many
        )} in
        mark_use id maybe_unique ienv
    | None -> Uenv.empty
  in
  let uenv1 = check_uniqueness_exp_ bo.bop_exp ienv in
  Uenv.seq uenv0 uenv1

let check_uniqueness_exp exp =
  let _ = check_uniqueness_exp_ exp Ienv.empty
  in ()

let check_uniqueness_value_bindings vbs =
  let _ = check_uniqueness_value_bindings_ vbs Ienv.empty
  in ()

let report_error = function
  | SharedUnique.CannotForce err ->
      let why_cannot_use_twice = match err.error with
        | `Uniqueness -> "This is used uniquely here"
        | `Linearity -> "This is defined as once"
      in
      let there_reason = match err.there.reason with
        | DirectUse -> Format.dprintf "which used as an alias"
        | MatchTupleWithVar _loc' ->
            Format.dprintf
                "which is used because the tuple containing it is matched to a variable"
      in
      let sub = [Location.msg ~loc:err.there.loc "%t" there_reason] in
      let here_reason = match err.here.reason with
      | DirectUse -> ""
      | MatchTupleWithVar _ -> "It is used because the tuple containing it is @ \
      matched to a variable."
      in
      begin
          Location.errorf ~loc:err.here.loc
            ~sub:sub
            "@[%s so cannot be used twice. %s Another use is @]" why_cannot_use_twice here_reason
      end
  | _ -> assert false

let report_error err =
  Printtyp.wrap_printing_env ~error:true Env.empty
    (fun () -> report_error err)

let () =
  Location.register_error_of_exn
    (function
      | SharedUnique.CannotForce err ->
          Some (report_error (SharedUnique.CannotForce err))
      | _ ->
          None
    )
