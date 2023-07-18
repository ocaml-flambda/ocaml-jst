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

(* Uniqueness analysis, ran after type-checking *)

open Asttypes
open Types
open Typedtree
module Uniqueness = Mode.Uniqueness
module Linearity = Mode.Linearity

module Occurrence = struct
  type t = { loc : Location.t }
  (** The occurrence of a potentially unique ident in the expression. Currently
  it's just the location; might add more things in the future *)
end

type axis = [ `Uniqueness | `Linearity ]

type boundary_reason =
  | Value_from_mod_class (* currently will never trigger *)
  | Free_var_of_mod_class (* currently will never trigger *)
  | Out_of_mod_class  (** See [report_error] for explanation *)

type error =
  | MultiUse of {
      here : Occurrence.t;  (** the occurrence that's failing forcing *)
      there : Occurrence.t;
          (** the other occurrence that triggers the forcing *)
      axis : axis;  (** which axis failed to force? *)
    }  (** Error caused by multiple use *)
  | Boundary of {
      occ : Occurrence.t;  (** The occurrence that's failing forcing*)
      axis : axis;  (** which axis failed to force? *)
      reason : boundary_reason;  (** which kind of boundary is being crossed? *)
    }
      (** Error caused by variable crossing the boundary of modules/classes. We
  conservatively make everything legacy at the boundary (i.e., shared and many).
  *)

exception Error of error

module Maybe_unique : sig
  type t
  (** The type representing a usage that could be either unique or shared *)

  val extract_occurrence : t -> Occurrence.t
  (** extract an arbitrary occurrence from this usage *)

  val singleton : unique_use -> Occurrence.t -> t
  (** construct a single usage *)

  val par : t -> t -> t

  val force_shared_multiuse : t -> there:Occurrence.t -> unit
  (** force this usage to be shared, due to multiple uses. [there] is the
      occurrence of the other usage. *)

  val force_shared_boundary : t -> reason:boundary_reason -> unit
  (** force this usage to be shared, due to boundary crossing. [reason] is,
      well, the reason *)

  val represented : t -> Mode.Uniqueness.t * Mode.Linearity.t
  (** returns the modes represented by this usage. *)
end = struct
  type t = (unique_use * Occurrence.t) list
  (** Occurrences with modes to be forced shared and many in the future if
      needed. This is a list because of multiple control flows. For example, if
      a value is used shared in one branch but unique in another branch, then
      overall the value is used uniquely (this is a "stricter" requirement).
      Therefore, techincally, the mode this list represents is the meet of all
      modes in the lists. (recall that shared > unique). Therefore, if this
      virtual mode needs to be forced shared, the whole list needs to be forced
      shared. *)

  let singleton unique_use occ : t = [ (unique_use, occ) ]

  let represented l =
    (* if any branch uses the value uniquely, then it is unique as a whole *)
    let uniqueness =
      Mode.Uniqueness.meet (List.map (fun ((uniq, _), _) -> uniq) l)
    in
    let linearity =
      Mode.Linearity.join (List.map (fun ((_, lin), _) -> lin) l)
    in
    (uniqueness, linearity)

  exception CannotForce of { occ : Occurrence.t; axis : axis }

  let force_shared l =
    let force_one ((uni, lin), occ) =
      (match Mode.Linearity.submode lin Mode.Linearity.many with
      | Ok () -> ()
      | Error () -> raise (CannotForce { occ; axis = `Linearity }));
      match Mode.Uniqueness.submode Mode.Uniqueness.shared uni with
      | Ok () -> ()
      | Error () -> raise (CannotForce { occ; axis = `Uniqueness })
    in
    List.iter force_one l

  let force_shared_multiuse t ~there =
    try force_shared t
    with CannotForce { occ; axis } ->
      raise (Error (MultiUse { here = occ; there; axis }))

  let force_shared_boundary t ~reason =
    try force_shared t
    with CannotForce { occ; axis } ->
      raise (Error (Boundary { occ; axis; reason }))

  let extract_occurrence = function [] -> assert false | (_, occ) :: _ -> occ
  let par l0 l1 = l0 @ l1
end

module Maybe_shared : sig
  type t
  (** The type representing a usage that could be either shared or borrowed *)

  val extract_occurrence : t -> Occurrence.t
  (** extract an arbitrary occurrence from the usage *)

  val set_barrier : t -> Uniqueness.t -> unit
  (** set the barrier. The uniqueness represents usage immediately following the
      current usage *)

  val par : t -> t -> t
  val singleton : unique_barrier ref -> Occurrence.t -> t
end = struct
  type t = (unique_barrier ref * Occurrence.t) list
  (** list of occurences together with modes to be forced as borrowed in the
  future if needed. It is a list because of multiple control flows. For
  example, if a value is used borrowed in one branch but shared in another,
  then the overall usage is shared. Therefore, the mode this list represents
  is the meet of all modes in the list. (recall that borrowed > shared).
  Therefore, if this virtual mode needs to be forced borrowed, the whole list
  needs to be forced borrowed. *)

  let par l0 l1 = l0 @ l1
  let singleton r occ = [ (r, occ) ]
  let extract_occurrence = function [] -> assert false | (_, occ) :: _ -> occ

  let set_barrier t uniq =
    List.iter
      (fun (barrier, _) ->
        match !barrier with
        | Some _ -> assert false
        | None -> barrier := Some uniq)
      t
end

module Usage = struct
  (* We have Unused (top) > Borrowed > Shared > Unique > Error (bot).

     - Unused means unused
     - Borrowed means read-only access confined to a region
     - Shared means read-only access that may escape a region. For example,
     storing the value in a cell that can be accessed later.
     - Unique means accessing the value as if it's the only pointer. Example
     includes overwriting.
     - Error means error happens when composing usage.

     Some observations:
     - It is sound to relax mode towards Error. It grants the access more
     "capability" and usually helps performance.
       For example, relaxing borrowed to shared allows code motion of
       projections. Relaxing shared to unique allows in-place update.

       An example of the relaxing borrowed to shared:

       let x = r.a in
       (a lot of codes)
       x

       In first line, r.memory_address is accessed as borrowed. But if we weaken
       it to shared and it still mode checks, that means
       - there is no "unique" access in the "a lot of codes"
       - or equivalently, that r.memory_address stays unchanged and safe to read

       and as a result, we can delay the projection at `x`.

       The downside of relaxing is the loss of completeness: if we relax too
       much the program will fail type check. In the extreme case we relax it to
       Error which fails type check outright (and extremely sound, hehe).

     - The purpose of this uniqueness analysis is to figure out the most relaxed
     mode for each use, such that we get the best performance, while still
     type-check. Currently there are really only two choices worth figuring out,
     Namely
     - borrowed or shared?
     - shared or unique?

     As a result, instead of having full-range inference, we only care about the
     following ranges:
     - unused
     - borrowed (Currently not useful, because we don't have explicit borrowing)
     - borrowed or shared
     - shared
     - shared or unique
     - error

     error is represented as exception which is just easier.
  *)
  type t =
    | Unused  (** empty usage *)
    | Borrowed of Occurrence.t
        (** A borrowed usage with an arbitrary occurrence. The occurrence is
        only for future error messages. Currently not used, because we don't
        have explicit borrowing *)
    | Maybe_shared of Maybe_shared.t
        (** A usage that could be either borrowed or shared. *)
    | Shared of Occurrence.t
        (** A shared usage with an arbitrary occurrence. The occurrence is only
        for future error messages. *)
    | Maybe_unique of Maybe_unique.t
        (** A usage that could be either unique or shared. *)

  let to_string = function
    | Unused -> "unused"
    | Borrowed _ -> "borrowed"
    | Maybe_shared _ -> "maybe_shared"
    | Shared _ -> "shared"
    | Maybe_unique _ -> "maybe_unique"

  let print ppf t = Format.fprintf ppf "%s" (to_string t)

  let _extract_occurrence = function
    | Unused -> assert false
    | Borrowed occ -> occ
    | Maybe_shared l -> Maybe_shared.extract_occurrence l
    | Shared occ -> occ
    | Maybe_unique l -> Maybe_unique.extract_occurrence l

  let par m0 m1 =
    match (m0, m1) with
    | Unused, m | m, Unused -> m
    | Borrowed _, t | t, Borrowed _ -> t
    | Maybe_shared l0, Maybe_shared l1 -> Maybe_shared (Maybe_shared.par l0 l1)
    | Maybe_shared _, t | t, Maybe_shared _ -> t
    | Shared _, t | t, Shared _ -> t
    | Maybe_unique l0, Maybe_unique l1 -> Maybe_unique (Maybe_unique.par l0 l1)

  let seq m0 m1 =
    match (m0, m1) with
    | Unused, m | m, Unused -> m
    | Borrowed _, t -> t
    | Maybe_shared _, Borrowed _ -> m0
    | Maybe_shared l0, Maybe_shared l1 -> Maybe_shared (Maybe_shared.par l0 l1)
    | Maybe_shared _, Shared _ -> m1
    | Maybe_shared l0, Maybe_unique l1 ->
        (* Four cases (semi-colon meaning sequential composition):
            Borrowed;Shared = Shared
            Borrowed;Unique = Unique
            Shared;Shared = Shared
            Shared;Unique = Error

            We are in a dilemma: recall that Borrowed->Shared allows code
            motion, and Shared->Unique allows unique overwriting. We can't have
            both. We first note is that the first is a soft optimization, and
            the second is a hard requirement.

            A reasonable solution is thus to check if the m1 actually needs
            to use the "unique" capabilities. If not, there is no need to
            relax it to Unique, and we will make it Shared, and make m0
            Shared for code-motion. However, there is no good way to do that,
            because the "unique_use" in "maybe_unique" is not complete,
            because the type-checking and uniqueness analysis is performed on
            a per-top-level-expr basis.

            Our solution is to record on the m0 that it is constrained by the
            m1. I.e. if m1 is Unique, then m0 cannot be Shared. After the type
            checking of the whole file, m1 will correctly tells whether it needs
            to be Unique, and by extension whether m0 can be Shared. *)
        let uniq, _ = Maybe_unique.represented l1 in
        Maybe_shared.set_barrier l0 uniq;
        m1
    | Shared _, Borrowed _ -> m0
    | Maybe_unique l, Borrowed occ ->
        Maybe_unique.force_shared_multiuse l ~there:occ;
        Shared occ
    | Shared _, Maybe_shared _ -> m0
    | Maybe_unique l0, Maybe_shared l1 ->
        (* Four cases:
            Shared;Borrowed = Shared
            Shared;Shared = Shared
            Unique;Borrowed = Error
            Unique;Shared = Error

            As you can see, we need to force the m0 to Shared, and m1 needn't
            be constrained. The result is always Shard.
        *)
        let occ = Maybe_shared.extract_occurrence l1 in
        Maybe_unique.force_shared_multiuse l0 ~there:occ;
        Shared occ
    | Shared _, Shared _ -> m0
    | Maybe_unique l, Shared occ | Shared occ, Maybe_unique l ->
        Maybe_unique.force_shared_multiuse l ~there:occ;
        Shared occ
    | Maybe_unique l0, Maybe_unique l1 ->
        let occ1 = Maybe_unique.extract_occurrence l1 in
        let occ0 = Maybe_unique.extract_occurrence l0 in
        Maybe_unique.force_shared_multiuse l0 ~there:occ1;
        Maybe_unique.force_shared_multiuse l1 ~there:occ0;
        Shared (Maybe_unique.extract_occurrence l0)
end

(** lifting module Usage to trees *)
module Usage_tree = struct
  module Projection = struct
    module T = struct
      (** Projections from parent to child. *)
      type t =
        | Tuple_field of int
        | Record_field of string
        | Construct_field of string * int
        | Variant_field of label
        (* TODO: it would be nicer to remove this memory_address thing for the
           following reason: Memory_address having Memory_address as child is
           non-sense and yet representable. Another reason: awkward in error
           message printing. The root cause of both reasons is that
           foo.Memory_address is not a child of foo, but foo itself.

           Instead we should represent Memory_address as a property on the value
           itself (instead of as its child). *)
        | Memory_address

      let print ppf = function
        | Tuple_field i -> Format.fprintf ppf ".%i" i
        | Record_field s -> Format.fprintf ppf ".%s" s
        | Construct_field (s, i) -> Format.fprintf ppf "|%s.%i" s i
        | Variant_field l -> Format.fprintf ppf "|%s" l
        | Memory_address -> Format.fprintf ppf ".*"

      let compare t1 t2 =
        match (t1, t2) with
        | Tuple_field i, Tuple_field j -> Int.compare i j
        | Record_field l1, Record_field l2 -> String.compare l1 l2
        | Construct_field (l1, i), Construct_field (l2, j) -> (
            match String.compare l1 l2 with 0 -> Int.compare i j | i -> i)
        | Variant_field l1, Variant_field l2 -> String.compare l1 l2
        | Memory_address, Memory_address -> 0
        | ( Tuple_field _,
            ( Record_field _ | Construct_field _ | Variant_field _
            | Memory_address ) ) ->
            -1
        | ( ( Record_field _ | Construct_field _ | Variant_field _
            | Memory_address ),
            Tuple_field _ ) ->
            1
        | Record_field _, (Construct_field _ | Variant_field _ | Memory_address)
          ->
            -1
        | (Construct_field _ | Variant_field _ | Memory_address), Record_field _
          ->
            1
        | Construct_field _, (Variant_field _ | Memory_address) -> -1
        | (Variant_field _ | Memory_address), Construct_field _ -> 1
        | Variant_field _, Memory_address -> -1
        | Memory_address, Variant_field _ -> 1
    end

    include T
    module Map = Map.Make (T)
  end

  type t = { children : t Projection.Map.t; usage : Usage.t }
  (** Represents a tree of usage. Each node records the par on all possible
     execution paths. As a result, trees such as `S -> U` is valid, even though
     it would be invalid if it was the result of a single path: using a parent
     shared and a child uniquely is obviously bad. Howerver, it might be the
     result of "par"ing multiple path: `S` par `N -> U`, which is valid.

     INVARIANT: children >= parent. For example, having a shared child under a
     unique parent is nonsense. The invariant is preserved because Usage.par and
     Usage.seq above is monotone, and Usage_tree.par and Usage_tree.seq here is
     node-wise. *)

  let rec print_children ppf children =
    Projection.Map.iter
      (fun proj child ->
        Format.fprintf ppf "%a = %a," Projection.print proj print child)
      children

  and print ppf t =
    Format.fprintf ppf "%a {%a}" Usage.print t.usage print_children t.children

  module Path = struct
    type t = Projection.t list

    let child (p : t) (a : Projection.t) : t = p @ [ a ]
    let root : t = []
    let _print ppf = Format.pp_print_list Projection.print ppf
  end

  let leaf usage = { usage; children = Projection.Map.empty }
  let empty = leaf Usage.Unused

  (* lift par and seq to trees *)
  let rec par t0 t1 =
    {
      usage = Usage.par t0.usage t1.usage;
      children =
        Projection.Map.merge
          (fun _proj c0 c1 ->
            let c0 = Option.value c0 ~default:t0 in
            let c1 = Option.value c1 ~default:t1 in
            Some (par c0 c1))
          t0.children t1.children;
    }

  let rec seq t0 t1 =
    let usage = Usage.seq t0.usage t1.usage in
    {
      usage;
      children =
        Projection.Map.merge
          (fun _proj c0 c1 ->
            let c0 = match c0 with None -> leaf t0.usage | Some c -> c in
            let c1 = match c1 with None -> leaf t1.usage | Some c -> c in
            Some (seq c0 c1))
          t0.children t1.children;
    }

  let rec singleton path leaf =
    match path with
    | [] -> { usage = leaf; children = Projection.Map.empty }
    | proj :: path ->
        {
          usage = Unused;
          children = Projection.Map.singleton proj (singleton path leaf);
        }

  (** f must be monotone *)
  let rec map f t =
    let usage = f t.usage in
    let children = Projection.Map.map (map f) t.children in
    { usage; children }
end

(** Lift Usage_tree to forest *)
module Usage_forest = struct
  module Root_id = struct
    module T = struct
      type t = { id : int; name : string }

      let compare t1 t2 = t1.id - t2.id
    end

    include T
    module Map = Map.Make (T)

    let stamp = ref 0

    let fresh name =
      let id = !stamp in
      stamp := id + 1;
      { id; name }

    let fresh_of_ident ident = fresh (Ident.name ident)
    let name t1 = t1.name
    let print ppf t = Format.fprintf ppf "%s" (name t)
  end

  type t = Usage_tree.t Root_id.Map.t
  (** Represents a forest of usage. *)

  let _print ppf t =
    Root_id.Map.iter
      (fun rootid tree ->
        Format.fprintf ppf "%a = %a, " Root_id.print rootid Usage_tree.print
          tree)
      t

  module Path = struct
    type t = Root_id.t * Usage_tree.Path.t

    let child ((rootid, path) : t) proj : t =
      (rootid, Usage_tree.Path.child path proj)

    let child_of_many paths proj = List.map (fun path -> child path proj) paths
    let fresh_root name : t = (Root_id.fresh name, Usage_tree.Path.root)

    let fresh_root_of_ident ident =
      (Root_id.fresh_of_ident ident, Usage_tree.Path.root)
  end

  let empty = Root_id.Map.empty

  let par : t -> t -> t =
   fun t0 t1 ->
    Root_id.Map.merge
      (fun _rootid t0 t1 ->
        let t0 = Option.value t0 ~default:Usage_tree.empty in
        let t1 = Option.value t1 ~default:Usage_tree.empty in
        Some (Usage_tree.par t0 t1))
      t0 t1

  let seq : t -> t -> t =
   fun t0 t1 ->
    Root_id.Map.merge
      (fun _rootid t0 t1 ->
        let t0 = Option.value t0 ~default:Usage_tree.empty in
        let t1 = Option.value t1 ~default:Usage_tree.empty in
        Some (Usage_tree.seq t0 t1))
      t0 t1

  let pars l = List.fold_left par empty l
  let seqs l = List.fold_left seq empty l

  let singleton ((rootid, path') : Path.t) leaf =
    Root_id.Map.singleton rootid (Usage_tree.singleton path' leaf)

  (** f must be monotone *)
  let map f = Root_id.Map.map (Usage_tree.map f)
end

module UF = Usage_forest

module Ienv = struct
  type t = UF.Path.t list Ident.Map.t
  (** Each identifier is mapped to a list of possible nodes, each represented by
     a path into the forest, instead of directly ponting to the node. *)

  (* used for [OR] patterns. This operation is commutative  *)
  let par ienv0 ienv1 =
    Ident.Map.merge
      (fun _id locs0 locs1 ->
        match (locs0, locs1) with
        | None, None -> assert false
        | None, Some t | Some t, None -> Some t
        | Some locs0, Some locs1 -> Some (locs0 @ locs1))
      ienv0 ienv1

  (* ienv0 is the old env; ienv1 is probably the new bindings to be added after
     pattern matching. ienv1 simply overwrite ienv0 *)
  let seq ienv0 ienv1 =
    Ident.Map.merge
      (fun _id locs0 locs1 ->
        match (locs0, locs1) with
        | None, None -> assert false
        | Some t, None -> Some t
        | _, Some t -> Some t)
      ienv0 ienv1

  let empty = Ident.Map.empty
  let seqs ienvs = List.fold_left seq empty ienvs
  let _pars ienvs = List.fold_left par empty ienvs
  let singleton id locs = Ident.Map.singleton id locs
end

type single_value_to_match = UF.Path.t list * Location.t * unique_use option
(** A triple of:
   - the value's all possible paths.
   - the location where it's defined
   - the modes, if it's actually an alias
*)

type value_to_match =
  | Match_tuple of single_value_to_match list
      (** The value being matched is a tuple; we treat it specially so matching
  tuples against tuples merely create alias instead of uses *)
  | Match_single of single_value_to_match
      (** The value being matched is not a tuple *)

let mark_implicit_borrow_memory_address_paths paths occ =
  let mark_one path =
    (* borrow the memory address of the parent *)
    UF.singleton
      (UF.Path.child path Usage_tree.Projection.Memory_address)
      (* Currently we just generate a dummy unique_barrier ref that won't be
         consumed. The distinction between implicit and explicit borrowing is
         still needed because they are handled differently in closures *)
      (Maybe_shared (Maybe_shared.singleton (ref None) occ))
  in
  UF.pars (List.map (fun path -> mark_one path) paths)

let _mark_borrow_paths paths occ =
  let mark_one path =
    (* borrow the memory address of the parent *)
    UF.singleton path
      (* Currently we just generate a dummy unique_barrier ref that won't be
         consumed. *)
      (Borrowed occ)
  in
  UF.pars (List.map (fun path -> mark_one path) paths)

let mark_implicit_borrow_memory_address = function
  | Match_single (paths, loc, _) ->
      mark_implicit_borrow_memory_address_paths paths { Occurrence.loc }
  (* it's still a tuple - we own it and nothing to do here *)
  | Match_tuple _ -> UF.empty

let _mark_shared paths occ =
  let mark_one path = UF.singleton path (Shared occ) in
  UF.pars (List.map (fun path -> mark_one path) paths)

let mark_maybe_unique paths unique_use occ =
  let mark_one path =
    UF.singleton path (Maybe_unique (Maybe_unique.singleton unique_use occ))
  in
  UF.pars (List.map (fun path -> mark_one path) paths)

(* returns:
   the updated value.
   the new introduced bindings.
   usage during the process
*)
let pattern_match_var ~loc id value =
  match value with
  | Match_single (paths, _, _) -> (value, Ienv.singleton id paths, UF.empty)
  | Match_tuple values ->
      let path = UF.Path.fresh_root_of_ident id in
      let ienv = Ienv.singleton id [ path ] in
      (* Mark all ps as seen, as we bind the tuple to a variable. *)
      (* Can we make it aliases instead of used? Hard to do if we want
         to preserve the tree-ness *)
      ( Match_single ([ path ], loc, None),
        ienv,
        UF.seqs
          (List.map
             (fun (paths, loc', modes) ->
               match modes with
               | None -> UF.empty
               | Some unique_use ->
                   let occ = { Occurrence.loc = loc' } in
                   mark_maybe_unique paths unique_use occ)
             values) )

(*
handling pattern match of value against pat, returns ienv and uf.
ienv is the new bindings introduced;
uf is the usage caused by the pattern matching *)
let rec pattern_match pat value =
  match pat.pat_desc with
  | Tpat_any -> (Ienv.empty, UF.empty)
  | Tpat_var (id, _, _) ->
      let _, ienv, uf = pattern_match_var ~loc:pat.pat_loc id value in
      (ienv, uf)
  | Tpat_alias (pat', id, _, _) ->
      let value, ienv0, uf0 = pattern_match_var ~loc:pat.pat_loc id value in
      let ienv1, uf1 = pattern_match pat' value in
      (Ienv.seq ienv0 ienv1, UF.seq uf0 uf1)
  | Tpat_constant _ -> (Ienv.empty, mark_implicit_borrow_memory_address value)
  | Tpat_tuple pats ->
      pat_proj
        ~handle_tuple:(fun values ->
          (* We matched a tuple against a tuple parent and descend into each
             case *)
          (* no borrowing needed - we own the tuple! *)
          let ienvs, ufs =
            List.split
              (List.map2
                 (fun pat value -> pattern_match pat (Match_single value))
                 pats values)
          in
          (Ienv.seqs ienvs, UF.seqs ufs))
        ~extract_pat:Fun.id
        ~mk_proj:(fun i _ -> Usage_tree.Projection.Tuple_field i)
        value pats
  | Tpat_construct (lbl, _, pats, _) ->
      pat_proj ~extract_pat:Fun.id
        ~mk_proj:(fun i _ ->
          Usage_tree.Projection.Construct_field (Longident.last lbl.txt, i))
        value pats
  | Tpat_variant (lbl, mpat, _) ->
      let uf = mark_implicit_borrow_memory_address value in
      let t =
        match value with
        | Match_single (paths, _, modes) ->
            ( UF.Path.child_of_many paths
                (Usage_tree.Projection.Variant_field lbl),
              pat.pat_loc,
              modes )
        | Match_tuple _ ->
            (* matching a tuple against variant can't pass type checking *)
            assert false
      in
      let ienv, uf' =
        match mpat with
        | Some pat' -> pattern_match pat' (Match_single t)
        | None -> (Ienv.empty, UF.empty)
      in
      (ienv, UF.seq uf uf')
  | Tpat_record (pats, _) ->
      pat_proj
        ~extract_pat:(fun (_, _, pat) -> pat)
        ~mk_proj:(fun _ (_, l, _) ->
          Usage_tree.Projection.Record_field l.lbl_name)
        value pats
  | Tpat_array (_, pats) -> (
      match value with
      | Match_tuple _ -> assert false
      | Match_single (paths, loc, _) ->
          let occ = { Occurrence.loc } in
          let uf = mark_implicit_borrow_memory_address_paths paths occ in
          let ienvs, ufs =
            List.split
              (List.map
                 (fun pat ->
                   let value =
                     Match_single
                       ([ UF.Path.fresh_root "array_field" ], loc, None)
                   in
                   pattern_match pat value)
                 pats)
          in
          (Ienv.seqs ienvs, UF.seqs (uf :: ufs)))
  | Tpat_lazy pat' -> pattern_match pat' value
  | Tpat_or (a, b, _) ->
      let ienv0, uf0 = pattern_match a value in
      let ienv1, uf1 = pattern_match b value in
      (* note that we use Ienv.par *)
      (Ienv.par ienv0 ienv1, UF.seq uf0 uf1)

and pat_proj :
      'a.
      ?handle_tuple:_ ->
      extract_pat:('a -> _) ->
      mk_proj:(_ -> 'a -> _) ->
      _ ->
      'a list ->
      _ =
 fun ?(handle_tuple = fun _ -> assert false) ~extract_pat ~mk_proj value pats ->
  match value with
  | Match_single (paths, loc, _) ->
      let occ = { Occurrence.loc } in
      let uf = mark_implicit_borrow_memory_address_paths paths occ in
      let ienvs, ufs =
        List.split
          (List.mapi
             (fun i patlike ->
               let proj = mk_proj i patlike in
               let paths = UF.Path.child_of_many paths proj in
               let t = (paths, loc, None) in
               pattern_match (extract_pat patlike) (Match_single t))
             pats)
      in
      (Ienv.seqs ienvs, UF.seqs (uf :: ufs))
  | Match_tuple values -> handle_tuple values

(* We ignore exceptions in uniqueness analysis. *)
let comp_pattern_match pat value =
  match split_pattern pat with
  | Some pat', _ -> pattern_match pat' value
  | None, _ -> (Ienv.empty, UF.empty)

let maybe_paths_of_ident ?maybe_unique ienv path =
  let force reason (unique_use, occ) =
    let maybe_unique = Maybe_unique.singleton unique_use occ in
    Maybe_unique.force_shared_boundary maybe_unique ~reason
  in
  match path with
  | Path.Pident id -> (
      match Ident.Map.find_opt id ienv with
      (* TODO: for better error message, we should record in ienv why some
         variables are not in it. *)
      | None ->
          Option.iter (force Out_of_mod_class) maybe_unique;
          None
      | Some paths -> Some paths)
  (* accessing a module, which is forced by typemod to be shared and many.
     Here we force it again just to be sure *)
  | Path.Pdot _ ->
      Option.iter (force Value_from_mod_class) maybe_unique;
      None
  | Path.Papply _ -> assert false

(* TODO: replace the dirty hack The following functions are dirty hack and used
   for modules and classes. Currently we treat the boundary between
   modules/classes and their surrounding environment coarsely. To be specific,
   all references in the modules/classes pointing to the environment are treated
   as many and shared. This translates to enforcement on both ends: - inside the
   module, those uses needs to be forced as many and shared - need a Usage_forest
   which marks those uses as many and shared, so that the parent expression can
   detect conflict if any.

   The following function returns all open variables inside a module. *)
let open_variables ienv f =
  let ll = ref [] in
  let iter =
    {
      Tast_iterator.default_iterator with
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_ident (path, _, _, _, unique_use) -> (
              match maybe_paths_of_ident ienv path with
              | None -> ()
              | Some paths ->
                  let occ = { Occurrence.loc = e.exp_loc } in
                  let maybe_unique = Maybe_unique.singleton unique_use occ in
                  ll := (paths, maybe_unique) :: !ll)
          | _ -> ());
          Tast_iterator.default_iterator.expr self e);
    }
  in
  f iter;
  !ll

(* The following function marks all open variables in a class/module as shared,
   as well as returning a UF reflecting all those shared usage. *)
let mark_shared_open_variables ienv f _loc =
  let ll = open_variables ienv f in
  let ufs =
    List.map
      (fun (paths, maybe_unique) ->
        (* the following force is not needed, because when UA is done on the
           module/class, maybe_paths_of_ident will force free variables to
           shared, because ienv given to it will not include the outside
           variables. We nevertheless force it here just to be sure *)
        Maybe_unique.force_shared_boundary maybe_unique
          ~reason:Free_var_of_mod_class;
        let shared =
          Usage.Shared (Maybe_unique.extract_occurrence maybe_unique)
        in
        let ufs = List.map (fun path -> UF.singleton path shared) paths in
        UF.seqs ufs)
      ll
  in
  UF.seqs ufs

(* There are two modes our algorithm will work at.

   In the first mode, we care about if the expression can be considered as
   alias, for example, we want `a.x.y` to return the alias of a.x.y in addition
   to the usage of borrowing a and a.x. Note that a.x.y is not included in the
   usage, and the caller is responsible to mark a.x.y if it is used.

   In the second mode, we don't care about if the expression can be considered
   as alias. Checking a.x.y will return the usage of borrowing a and a.x, and
   using a.x.y. This mode is used in most occasions. *)

(* the following function corresponds to the second mode *)
let rec check_uniqueness_exp_ exp (ienv : Ienv.t) : UF.t =
  let loc = exp.exp_loc in
  match exp.exp_desc with
  | Texp_ident _ -> (
      match check_uniqueness_exp' exp ienv with
      | Some (paths, unique_use), uf ->
          let occ = { Occurrence.loc } in
          UF.seq uf (mark_maybe_unique paths unique_use occ)
      | None, uf -> uf)
  | Texp_constant _ -> UF.empty
  | Texp_let (_, vbs, exp') ->
      let ienv', uf = check_uniqueness_value_bindings_ vbs ienv in
      let uf' = check_uniqueness_exp_ exp' (Ienv.seq ienv ienv') in
      UF.seq uf uf'
  | Texp_function { param; cases } ->
      (* `param` is only a hint not a binder;
         actual binding done in cases by Tpat_var and Tpat_alias *)
      let value =
        Match_single ([ UF.Path.fresh_root_of_ident param ], loc, None)
      in
      let uf = check_uniqueness_cases value cases ienv in
      (* we are constructing a closure here, and therefore any borrowing of free
         variables in the closure is in fact using shared. *)
      UF.map
        (function
          | Maybe_shared l ->
              (* implicit borrowing lifted. *)
              Shared (Maybe_shared.extract_occurrence l)
              (* other usage stays the same *)
          | m -> m)
        uf
  | Texp_apply (f, xs, _, _) ->
      let uf = check_uniqueness_exp_ f ienv in
      let ufs =
        List.map
          (fun (_, arg) ->
            match arg with
            | Arg e -> check_uniqueness_exp_ e ienv
            | Omitted _ -> UF.empty)
          xs
      in
      UF.seqs (uf :: ufs)
  | Texp_match (e, _, cs, _) ->
      let value, uf = init_value_to_match e ienv in
      let uf' = check_uniqueness_comp_cases value cs ienv in
      UF.seq uf uf'
  | Texp_try (e, cs) ->
      let value, uf = init_value_to_match e ienv in
      let uf' = check_uniqueness_cases value cs ienv in
      (* we don't know how much of e will be run; safe to assume all of them *)
      UF.seq uf uf'
  | Texp_tuple (es, _) ->
      UF.seqs (List.map (fun e -> check_uniqueness_exp_ e ienv) es)
  | Texp_construct (_, _, es, _) ->
      UF.seqs (List.map (fun e -> check_uniqueness_exp_ e ienv) es)
  | Texp_variant (_, None) -> UF.empty
  | Texp_variant (_, Some (e, _)) -> check_uniqueness_exp_ e ienv
  | Texp_record { fields; extended_expression } -> (
      let check_fields =
        UF.seqs
          (Array.to_list
             (Array.map
                (fun field ->
                  match field with
                  | _, Kept _ -> UF.empty
                  | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv)
                fields))
      in
      match extended_expression with
      | None -> check_fields
      | Some exp -> (
          let value, uf0 = check_uniqueness_exp' exp ienv in
          match value with
          | None ->
              check_fields
              (* {exp with ...}; don't know anything about exp so nothing we can
                 do here*)
          | Some (ps, unique_use) ->
              (* {x with ...} *)
              let ufs =
                Array.map
                  (fun field ->
                    match field with
                    | l, Kept _ ->
                        let ps =
                          UF.Path.child_of_many ps
                            (Usage_tree.Projection.Record_field l.lbl_name)
                        in
                        let occ = { Occurrence.loc } in
                        mark_maybe_unique ps unique_use occ
                    | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv)
                  fields
              in
              let uf1 = UF.seqs (Array.to_list ufs) in
              UF.seq uf0 uf1))
  | Texp_field _ -> (
      match check_uniqueness_exp' exp ienv with
      | Some (ps, unique_use), uf ->
          let occ = { Occurrence.loc } in
          UF.seq uf (mark_maybe_unique ps unique_use occ)
      | None, uf -> uf)
  | Texp_setfield (exp', _, _, _, e) -> (
      (* setfield is understood as an opaque function which borrows the memory
         address of the record *)
      let uf = check_uniqueness_exp_ e ienv in
      match check_uniqueness_exp' exp' ienv with
      | None, uf' -> UF.seq uf uf'
      | Some (ps, _), uf' ->
          let occ = { Occurrence.loc } in
          UF.seqs [ uf; uf'; mark_implicit_borrow_memory_address_paths ps occ ])
  | Texp_array (_, es, _) ->
      UF.seqs (List.map (fun e -> check_uniqueness_exp_ e ienv) es)
  | Texp_ifthenelse (if', then', else_opt) ->
      (* if' is only borrowed, not used; but probably doesn't matter because of
         mode crossing *)
      let uf0 = check_uniqueness_exp_ if' ienv in
      let uf1 =
        match else_opt with
        | Some else' ->
            UF.par
              (check_uniqueness_exp_ then' ienv)
              (check_uniqueness_exp_ else' ienv)
        | None -> check_uniqueness_exp_ then' ienv
      in
      let uf = UF.seq uf0 uf1 in
      uf
  | Texp_sequence (e, _, e') ->
      let uf0 = check_uniqueness_exp_ e ienv in
      let uf1 = check_uniqueness_exp_ e' ienv in
      UF.seq uf0 uf1
  | Texp_while { wh_cond; wh_body; _ } ->
      let uf0 = check_uniqueness_exp_ wh_cond ienv in
      let uf1 = check_uniqueness_exp_ wh_body ienv in
      UF.seq uf0 uf1
  | Texp_list_comprehension { comp_body; comp_clauses } ->
      let uf0 = check_uniqueness_exp_ comp_body ienv in
      let uf1 = check_uniqueness_comprehensions comp_clauses ienv in
      UF.seq uf0 uf1
  | Texp_array_comprehension (_, { comp_body; comp_clauses }) ->
      let uf0 = check_uniqueness_exp_ comp_body ienv in
      let uf1 = check_uniqueness_comprehensions comp_clauses ienv in
      UF.seq uf0 uf1
  | Texp_for { for_from; for_to; for_body; _ } ->
      let uf0 = check_uniqueness_exp_ for_from ienv in
      let uf1 = check_uniqueness_exp_ for_to ienv in
      let uf2 = check_uniqueness_exp_ for_body ienv in
      UF.seqs [ uf0; uf1; uf2 ]
  | Texp_send (e, _, _, _) -> check_uniqueness_exp_ e ienv
  | Texp_new _ -> UF.empty
  | Texp_instvar _ -> UF.empty
  | Texp_setinstvar (_, _, _, e) -> check_uniqueness_exp_ e ienv
  | Texp_override (_, ls) ->
      UF.seqs (List.map (fun (_, _, e) -> check_uniqueness_exp_ e ienv) ls)
  | Texp_letmodule (_, _, _, mod_expr, e) ->
      let uf =
        mark_shared_open_variables ienv
          (fun iter -> iter.module_expr iter mod_expr)
          mod_expr.mod_loc
      in
      UF.seq uf (check_uniqueness_exp_ e ienv)
  | Texp_letexception (_, e) -> check_uniqueness_exp_ e ienv
  | Texp_assert e -> check_uniqueness_exp_ e ienv
  | Texp_lazy e -> check_uniqueness_exp_ e ienv
  | Texp_object (cls_struc, _) ->
      (* the object (methods, values) will be type-checked by Typeclass,
         which invokes uniqueness check.*)
      mark_shared_open_variables ienv
        (fun iter -> iter.class_structure iter cls_struc)
        exp.exp_loc
  | Texp_pack mod_expr ->
      (* the module will be type-checked by Typemod which invokes uniqueness
         analysis. *)
      mark_shared_open_variables ienv
        (fun iter -> iter.module_expr iter mod_expr)
        mod_expr.mod_loc
  | Texp_letop { let_; ands; body } ->
      let uf0 = check_uniqueness_binding_op let_ exp ienv in
      let ufs1 =
        List.map (fun bop -> check_uniqueness_binding_op bop exp ienv) ands
      in
      let uf2 =
        check_uniqueness_cases
          (Match_single ([ UF.Path.fresh_root "letop" ], loc, None))
          [ body ] ienv
      in
      UF.seqs ((uf0 :: ufs1) @ [ uf2 ])
  | Texp_unreachable -> UF.empty
  | Texp_extension_constructor _ -> UF.empty
  | Texp_open (open_decl, e) ->
      let uf =
        mark_shared_open_variables ienv
          (fun iter -> iter.open_declaration iter open_decl)
          open_decl.open_loc
      in
      UF.seq uf (check_uniqueness_exp_ e ienv)
  | Texp_probe { handler } -> check_uniqueness_exp_ handler ienv
  | Texp_probe_is_enabled _ -> UF.empty
  | Texp_exclave e -> check_uniqueness_exp_ e ienv

(*
This function corresponds to the first mode.

Look at exp and see if it can be treated as alias currently only texp_ident and
texp_field (and recursively so) are treated so. return paths and modes. paths is
the list of possible memory locations. returns None if exp is not alias, which
also implies that the usage of exp is included in the returned uf. *)
and check_uniqueness_exp' exp ienv : (UF.Path.t list * unique_use) option * UF.t
    =
  match exp.exp_desc with
  | Texp_ident (p, _, _, _, unique_use) -> (
      let occ = { Occurrence.loc = exp.exp_loc } in
      let maybe_unique = (unique_use, occ) in
      match maybe_paths_of_ident ~maybe_unique ienv p with
      | None -> (None, UF.empty)
      | Some ps -> (Some (ps, unique_use), UF.empty))
  | Texp_field (e, _, l, modes, _) -> (
      match check_uniqueness_exp' e ienv with
      | Some (paths, _), uf ->
          (* accessing the field meaning borrowing the parent record's mem
             block. Note that the field itself is not borrowed or used *)
          let occ = { Occurrence.loc = e.exp_loc } in
          let uf' = mark_implicit_borrow_memory_address_paths paths occ in
          let paths' =
            UF.Path.child_of_many paths
              (Usage_tree.Projection.Record_field l.lbl_name)
          in
          (Some (paths', modes), UF.seq uf uf')
      | None, uf -> (None, uf))
  (* CR-someday anlorenzen: This could also support let-bindings. *)
  | _ -> (None, check_uniqueness_exp_ exp ienv)

and init_single_value_to_match exp ienv : single_value_to_match * UF.t =
  match check_uniqueness_exp' exp ienv with
  | Some (ps, pp), uf -> ((ps, exp.exp_loc, Some pp), uf)
  | None, uf -> (([ UF.Path.fresh_root "match" ], exp.exp_loc, None), uf)

(* take typed expression, do some parsing and give init_value_to_match *)
and init_value_to_match exp ienv =
  match exp.exp_desc with
  | Texp_tuple (es, _) ->
      let ps, ufs =
        List.split (List.map (fun e -> init_single_value_to_match e ienv) es)
      in
      (Match_tuple ps, UF.seqs ufs)
  | _ ->
      let s, uf = init_single_value_to_match exp ienv in
      (Match_single s, uf)

(* returns ienv and uf
   ienv is the new bindings introduced;
   uf is the usage forest caused by the binding
*)
and check_uniqueness_value_bindings_ vbs ienv =
  (* we imitate how data are accessed at runtime *)
  let ienvs, ufs =
    List.split
      (List.map
         (fun vb ->
           let value, uf = init_value_to_match vb.vb_expr ienv in
           let ienv, uf' = pattern_match vb.vb_pat value in
           (ienv, UF.seq uf uf'))
         vbs)
  in
  (Ienv.seqs ienvs, UF.seqs ufs)

(* type signature needed because high-ranked *)
and check_uniqueness_cases_ :
      'a.
      ('a Typedtree.general_pattern -> value_to_match -> Ienv.t * UF.t) ->
      value_to_match ->
      'a case list ->
      Ienv.t ->
      UF.t =
 fun ptm value cases ienv ->
  (* In the following we imitate how data are accessed at runtime for cases *)
  (* we first evaluate all LHS including all the guards, _sequentially_ *)
  let ienvs, ufs0 =
    List.split
      (List.map
         (fun case ->
           let ienv', uf = ptm case.c_lhs value in
           let uf' =
             match case.c_guard with
             | None -> UF.empty
             | Some g -> check_uniqueness_exp_ g (Ienv.seq ienv ienv')
           in
           (ienv', UF.seq uf uf'))
         cases)
  in
  (* we then evaluate all RHS, in _parallel_ *)
  let ufs1 =
    List.map2
      (fun ienv' case -> check_uniqueness_exp_ case.c_rhs (Ienv.seq ienv ienv'))
      ienvs cases
  in
  UF.seq (UF.seqs ufs0) (UF.pars ufs1)

and check_uniqueness_cases value cases ienv =
  check_uniqueness_cases_ pattern_match value cases ienv

and check_uniqueness_comp_cases value cases ienv =
  check_uniqueness_cases_ comp_pattern_match value cases ienv

and check_uniqueness_comprehensions cs ienv =
  UF.seqs
    (List.map
       (fun c ->
         match c with
         | Texp_comp_when e -> check_uniqueness_exp_ e ienv
         | Texp_comp_for cbs ->
             UF.seqs
               (List.map
                  (fun cb ->
                    match cb.comp_cb_iterator with
                    | Texp_comp_range { start; stop; _ } ->
                        let uf0 = check_uniqueness_exp_ start ienv in
                        let uf1 = check_uniqueness_exp_ stop ienv in
                        UF.seq uf0 uf1
                    | Texp_comp_in { sequence; _ } ->
                        check_uniqueness_exp_ sequence ienv)
                  cbs))
       cs)

and check_uniqueness_binding_op bo exp ienv =
  let uf0 =
    match maybe_paths_of_ident ienv bo.bop_op_path with
    | Some paths ->
        let occ = { Occurrence.loc = exp.exp_loc } in
        let unique_use = (Uniqueness.shared, Linearity.many) in
        mark_maybe_unique paths unique_use occ
    | None -> UF.empty
  in
  let uf1 = check_uniqueness_exp_ bo.bop_exp ienv in
  UF.seq uf0 uf1

let check_uniqueness_exp exp =
  let _ = check_uniqueness_exp_ exp Ienv.empty in
  ()

let check_uniqueness_value_bindings vbs =
  let _ = check_uniqueness_value_bindings_ vbs Ienv.empty in
  ()

let report_error = function
  | MultiUse { here; there; axis } ->
      let why_cannot_use_twice =
        match axis with
        | `Uniqueness -> "used uniquely here"
        | `Linearity -> "defined as once"
      in
      let sub = [ Location.msg ~loc:there.loc "" ] in
      Location.errorf ~loc:here.loc ~sub
        "@[This is %s so cannot be used twice. Another use is @]"
        why_cannot_use_twice
  | Boundary { occ; axis; reason } ->
      let reason =
        match reason with
        | Value_from_mod_class -> "another module or class"
        | Free_var_of_mod_class -> "outside the current module or class"
        | Out_of_mod_class -> "outside the current module or class"
      in
      let error =
        match axis with
        | `Uniqueness -> "This value is shared but used as unique"
        | `Linearity -> "This value is once but used as many"
      in
      Location.errorf ~loc:occ.loc "@[%s.\nHint: This value comes from %s.@]"
        error reason

let report_error err =
  Printtyp.wrap_printing_env ~error:true Env.empty (fun () -> report_error err)

let () =
  Location.register_error_of_exn (function
    | Error e -> Some (report_error e)
    | _ -> None)
