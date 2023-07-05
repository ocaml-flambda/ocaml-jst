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
  (* The occurrence of a potentially unique ident in the expression. *)
  type reason =
    | DirectUse (* it is used directly *)
    | MatchTupleWithVar of Location.t
  (* When matching on a tuple, we do not construct a tuple and match on it,
      but rather match on the individual elements of the tuple -- this preserves
      their uniqueness. But in a pattern an alias to the tuple could be created,
      in which case we have to construct the tuple and retroactively mark the
      elements as seen.
      Location points to the Tpat_var or Tpat_alias *)

  type t = { loc : Location.t; reason : reason }
end

module SharedUnique = struct
  (* auxilary module. See module Usage*)

  (* which axis cannot be forced? *)
  type error = [ `Uniqueness | `Linearity ]

  exception CannotForce of { occ : Occurrence.t; error : error }

  exception
    MultiUse of {
      (* the occurrence that's failing forcing *)
      here : Occurrence.t;
      (* the other occurrence that triggers the forcing *)
      there : Occurrence.t;
      (* which axis failed to force? *)
      error : error;
    }

  type reason =
    | ValueFromModClass (* currently will never trigger *)
    | FreeVariableOfModClass (* currently will never trigger *)
    | JustTopLevel

  exception TopLevel of { occ : Occurrence.t; error : error; reason : reason }

  type t =
    (* if already shared, we only need an occurrence for future error messages *)
    | Shared of Occurrence.t
    (* Occurrences with modes to be forced shared and many in the future
       if needed. This is a list because of multiple control flows. For example, if
       a value is used shared in one branch but unique in another branch, then
       overall the value is used uniquely (this is a "stricter" requirement).
       Therefore, techincally, the mode this list represents is the meet of all
       modes in the lists. (recall that shared > unique). Therefore, if this
       virtual mode needs to be forced shared, the whole list needs to be
       forced shared. *)
    | MaybeUnique of (unique_use * Occurrence.t) list

  let to_string = function
    | Shared _ -> "shared"
    | MaybeUnique _ -> "maybe_unique"

  let force t =
    match t with
    | Shared _ -> t
    | MaybeUnique l ->
        let force_one ((uni, lin), occ) =
          (match Mode.Linearity.submode lin Mode.Linearity.many with
          | Ok () -> ()
          | Error () -> raise (CannotForce { occ; error = `Linearity }));
          match Mode.Uniqueness.submode Mode.Uniqueness.shared uni with
          | Ok () -> ()
          | Error () -> raise (CannotForce { occ; error = `Uniqueness })
        in
        List.iter force_one l;
        let _, occ = List.hd l in
        Shared occ

  let force_multiuse t there =
    try force t
    with CannotForce { occ; error } ->
      raise (MultiUse { here = occ; there; error })

  let force_toplevel t reason =
    try force t
    with CannotForce { occ; error } -> raise (TopLevel { occ; error; reason })

  let par t0 t1 =
    match (t0, t1) with
    | Shared _, t | t, Shared _ -> t
    | MaybeUnique l0, MaybeUnique l1 -> MaybeUnique (l0 @ l1)

  let extract_occurrence = function
    | Shared occ -> occ
    | MaybeUnique ((_, occ) :: _) -> occ
    | MaybeUnique [] -> assert false

  let seq m0 m1 =
    let m0 = force_multiuse m0 (extract_occurrence m1) in
    let m1 = force_multiuse m1 (extract_occurrence m0) in
    m1
end

module BorrowedShared = struct
  (* auxilary module, see module Usage *)
  type t =
    (* if already borrowed, only need one occurrence for future error messages
    *)
    (* This constructor currently not used, because we don't have explicit borrowing *)
    | Borrowed of Occurrence.t
    (* list of occurences together with modes to be forced as borrowed in the
       future if needed. It is a list because of multiple control flows. For
       example, if a value is used borrowed in one branch but shared in another,
       then the overall usage is shared. Therefore, the mode this list represents
       is the meet of all modes in the list. (recall that borrowed > shared).
       Therefore, if this virtual mode needs to be forced borrowed, the whole list
       needs to be forced borrowed.
    *)
    | MaybeShared of (unique_barrier ref * Occurrence.t) list

  let to_string = function
    | Borrowed _ -> "borrowed"
    | MaybeShared _ -> "maybe_shared"

  let extract_occurrence = function
    | Borrowed occ -> occ
    | MaybeShared ((_, occ) :: _) -> occ
    | MaybeShared [] -> assert false

  let par t0 t1 =
    match (t0, t1) with
    | Borrowed _, t | t, Borrowed _ -> t
    | MaybeShared l0, MaybeShared l1 -> MaybeShared (l0 @ l1)

  let seq t0 t1 =
    match (t0, t1) with
    | Borrowed _, t -> t
    | MaybeShared s, Borrowed _ -> MaybeShared s
    | MaybeShared l0, MaybeShared l1 -> MaybeShared (l0 @ l1)
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
       For example, relaxing borrowed to shared allows code motion of projections.
       Relaxing shared to unique allows in-place update.

       An example of the relaxing borrowed to shared:

       let x = r.a in
       (a lot of codes)
       x

       In first line, r.memory_address is accessed as borrowed. But if we weaken
       it to shared and it still mode checks, that means
       - there is no "unique" access in the "a lot of codes"
       - or equivalently, that r.memory_address stays unchanged and safe to read

       and as a result, we can delay the projection at `x`.

       The downside of relaxing is the loss of completeness: if we relax too much
       the program will fail type check. In the extreme case we relax it to Error
       which fails type check outright (and extremely sound, hehe).

     - The purpose of this uniqueness analysis is to figure out the most relaxed mode
     for each use, such that we get the best performance, while still type-check.
     Currently there are really only two choices worth figuring out, Namely
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
    | Unused
    (* no good reason to factor out the two, except just to separating the code *)
    | BorrowedShared of BorrowedShared.t
    | SharedUnique of SharedUnique.t

  let to_string = function
    | Unused -> "unused"
    | BorrowedShared s -> BorrowedShared.to_string s
    | SharedUnique s -> SharedUnique.to_string s

  let print ppf t = Format.fprintf ppf "%s" (to_string t)

  let extract_occurrence = function
    | Unused -> assert false
    | BorrowedShared t -> BorrowedShared.extract_occurrence t
    | SharedUnique t -> SharedUnique.extract_occurrence t

  (* parallel composition, for composing multiple control flows *)
  let par m0 m1 =
    match (m0, m1) with
    | Unused, m | m, Unused -> m
    | BorrowedShared m0, BorrowedShared m1 ->
        BorrowedShared (BorrowedShared.par m0 m1)
    | BorrowedShared _, m | m, BorrowedShared _ ->
        m (* m must be sharedunique *)
    | SharedUnique m0, SharedUnique m1 -> SharedUnique (SharedUnique.par m0 m1)

  (* sequential composition *)
  let seq m0 m1 =
    match (m0, m1) with
    | Unused, m | m, Unused -> m
    | BorrowedShared m0, BorrowedShared m1 ->
        BorrowedShared (BorrowedShared.seq m0 m1)
    | BorrowedShared m0, SharedUnique m1 -> (
        match (m0, m1) with
        | Borrowed _, Shared _ -> SharedUnique m1
        | Borrowed _, MaybeUnique _ -> SharedUnique m1
        | MaybeShared _, Shared _ -> SharedUnique m1
        | MaybeShared l0, MaybeUnique l1 ->
            (* four cases:
               B;S = S
               B;U = U
               S;S = S
               S;U /=

               We are in a dilemma: recall that B->S allows code motion, and S->U allows
               unique overwriting. We can't have both. We first note is that the
               first is a soft optimization, and the second is a hard requirement.

               A reasonable solution is thus to
               check if the RHS actually needs to use the "unique" capabilities. If
               not, there is no need to relax it to unique, and we will make
               it shared, and make LHS shared for code-motion. However, there is no
               good way to do that, because the "unique_use" in "maybe_unique" is
               not complete, because the type-checking and uniqueness analysis is
               performed on a per-top-level-expr basis.

               Our solution is to record on the l0 that it is constrained by the l1.
               I.e. if any of l1 is U, then each of l0 cannot be S. After the type
               checking of the whole file, l1 will correctly tells whether it needs
               to be unique, and by extension whether l0 can be shared. *)
            let uniqs = List.map (fun ((uniq, _), _) -> uniq) l1 in
            (* if any of l1 is unique, then all of l0 must be borrowed *)
            let uniq = Mode.Uniqueness.meet uniqs in
            List.iter
              (fun (barrier, _) ->
                match !barrier with
                | Some _ -> assert false
                | None -> barrier := Some uniq)
              l0;
            SharedUnique m1)
    | SharedUnique m0, BorrowedShared m1 -> (
        match (m0, m1) with
        | Shared _, Borrowed _ -> SharedUnique m0
        | MaybeUnique _, Borrowed _ ->
            SharedUnique
              (SharedUnique.force_multiuse m0
                 (BorrowedShared.extract_occurrence m1))
        | Shared _, MaybeShared _ -> SharedUnique m0
        | MaybeUnique _, MaybeShared _ ->
            (* four cases:
               S;B = S
               S;S = S
               U;B /=
               U;S /=

               as you can see, we need to force the m0 to shared, and m1 needn't
               be constrained. The result is always S.
            *)
            SharedUnique
              (SharedUnique.force_multiuse m0
                 (BorrowedShared.extract_occurrence m1)))
    | SharedUnique m0, SharedUnique m1 -> SharedUnique (SharedUnique.seq m0 m1)
end

module UsageTree = struct
  (* lift Usage to trees *)
  module Projection = struct
    (* Projections from parent to child. *)
    module T = struct
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

      (* hopefully this function is injective *)
      let print ppf = function
        | Tuple_field i -> Format.fprintf ppf ".%i" i
        | Record_field s -> Format.fprintf ppf ".%s" s
        | Construct_field (s, i) -> Format.fprintf ppf "|%s.%i" s i
        | Variant_field l -> Format.fprintf ppf "|%s" l
        | Memory_address -> Format.fprintf ppf ".*"

      let human_readable ppf = function
        | Tuple_field i ->
            Format.fprintf ppf "the position-%i element of the tuple" i
        | Record_field s ->
            Format.fprintf ppf "the field \"%s\" of the record" s
        | Construct_field (s, i) ->
            Format.fprintf ppf
              "the position-%i element of the constructor \"%s\" in the value" i
              s
        | Variant_field l ->
            Format.fprintf ppf "the field \"%s\" of the variant" l
        | Memory_address -> Format.fprintf ppf ""

      let to_string (t : t) = Format.asprintf "%a" print t

      (* Yes, compare based on string is bad, but it saves 20
         lines of spaghetti code. Also I believe to_string is injective so it might
         actaully be fine. *)
      let compare t1 t2 = String.compare (to_string t1) (to_string t2)
    end

    include T
    module Map = Map.Make (T)
  end

  type relation = Ancestor | Descendant

  (* Tree:
     Each node records the par on all possible execution paths. As a result,
     trees such as `S -> U` is valid, even though it would be invalid if it was
     the result of a single path: using a parent shared and a child uniquely is
     obviously bad. Howerver, it might be the result of "par"ing multiple path:
     `S` par `N -> U`, which is valid.
  *)

  (* INVARIANT: children >= parent. For example, having a shared child under a
     unique parent is nonsense. The invariant is preserved because Usage.par and
     Usage.seq above is monotone, and UsageTree.par and UsageTree.seq here is
  node-wise. *)
  type t = { children : t Projection.Map.t; usage : Usage.t }

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

    let human_readable ppf t =
      Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.fprintf ppf " which is ")
        Projection.human_readable ppf t
  end

  exception
    MultiUse of {
      (* the occurrence that's failing forcing *)
      here : Occurrence.t;
      (* the other occurrence for reference *)
      there : Occurrence.t;
      (* which axis failed to force? *)
      error : SharedUnique.error;
      (* descentdant means there is a descendant of here *)
      there_is_of_here : relation;
      (* path from the ancestor to the descendant, reversed *)
      path : Path.t;
    }

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

  (* projs0 is the list of projections for t0.
     It is from the ancestor that t0.usage actually comes from,
     to t0.*)
  let rec seq t0 projs0 t1 projs1 =
    let usage =
      try Usage.seq t0.usage t1.usage
      with SharedUnique.MultiUse { here; there; error } ->
        (* t' is ancestor *)
        let t', path =
          match (projs0, projs1) with
          | [], _ -> (t1.usage, projs1)
          | _, [] -> (t0.usage, projs0)
          | _, _ -> assert false
        in
        let there_is_of_here =
          if (Usage.extract_occurrence t').loc = here.loc then Descendant
          else Ancestor
        in
        raise (MultiUse { here; there; error; there_is_of_here; path })
    in
    {
      usage;
      children =
        Projection.Map.merge
          (fun proj c0 c1 ->
            let c0, projs0 =
              match c0 with
              | None -> (leaf t0.usage, proj :: projs0)
              | Some c -> (c, [])
            in
            let c1, projs1 =
              match c1 with
              | None -> (leaf t1.usage, proj :: projs1)
              | Some c -> (c, [])
            in
            Some (seq c0 projs0 c1 projs1))
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

  let map f t =
    let rec loop acc t =
      (* to ensure the tree invariant: children >= parent *)
      let usage = Usage.par acc (f t.usage) in
      let children = Projection.Map.map (loop usage) t.children in
      { usage; children }
    in
    loop Usage.Unused t
end

module UsageForest = struct
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

  (* maps rootid to trees; contains only the roots *)
  type t = UsageTree.t Root_id.Map.t

  let _print ppf t =
    Root_id.Map.iter
      (fun rootid tree ->
        Format.fprintf ppf "%a = %a, " Root_id.print rootid UsageTree.print tree)
      t

  module Path = struct
    type t = Root_id.t * UsageTree.Path.t

    let child ((rootid, path) : t) proj : t =
      (rootid, UsageTree.Path.child path proj)

    let child_of_many paths proj = List.map (fun path -> child path proj) paths
    let fresh_root name : t = (Root_id.fresh name, UsageTree.Path.root)
    let fresh_root_of_id id = (Root_id.fresh_of_ident id, UsageTree.Path.root)
  end

  let empty = Root_id.Map.empty

  let par : t -> t -> t =
   fun t0 t1 ->
    Root_id.Map.merge
      (fun _rootid t0 t1 ->
        let t0 = Option.value t0 ~default:UsageTree.empty in
        let t1 = Option.value t1 ~default:UsageTree.empty in
        Some (UsageTree.par t0 t1))
      t0 t1

  let seq : t -> t -> t =
   fun t0 t1 ->
    Root_id.Map.merge
      (fun _rootid t0 t1 ->
        let t0 = Option.value t0 ~default:UsageTree.empty in
        let t1 = Option.value t1 ~default:UsageTree.empty in
        Some (UsageTree.seq t0 [] t1 []))
      t0 t1

  let pars l = List.fold_left par empty l
  let seqs l = List.fold_left seq empty l

  let singleton ((rootid, path') : Path.t) leaf =
    Root_id.Map.singleton rootid (UsageTree.singleton path' leaf)

  let map f t = Root_id.Map.map (UsageTree.map f) t
end

(* easier spelling *)
module UF = UsageForest

module Ienv = struct
  (* idents are mapped to multiple possible nodes, each represented by
     a path into the forest, instead of directly ponting to the node. *)

  type t = UF.Path.t list Ident.Map.t

  (* used for or patterns. This operation is commutative  *)
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


(* A tuple of:
   First is the value's all possible paths.
   Second is the location where it's defined.
   Third is the modes, if it's actually an alias
*)
type single_value_to_match = UF.Path.t list * Location.t * unique_use option

(* represent value to be match *)
type value_to_match =
  (* first is the special case of tuples; we treat it specially so matching
     tuples against tuples merely create alias instead of uses *)
  | MatchTuple of single_value_to_match list
  | MatchSingle of single_value_to_match

let mark_implicit_borrow_memory_address_paths paths occ =
  let mark_one path =
    (* borrow the memory address of the parent *)
    UF.singleton
      (UF.Path.child path UsageTree.Projection.Memory_address)
      (* Currently we just generate a dummy unique_barrier ref that won't be
         consumed. The distinction between implicit and explicit borrowing is still
         needed because they are handled differently in closures *)
      (BorrowedShared (MaybeShared [ (ref None, occ) ]))
  in
  UF.pars (List.map (fun path -> mark_one path) paths)

let mark_borrowed paths occ =
  let mark_one path = UF.singleton path (BorrowedShared (Borrowed occ)) in
  UF.pars (List.map (fun path -> mark_one path) paths)

let _mark_borrowed_ienv ienv occ =
  Ident.Map.fold
    (fun _ paths acc -> UF.seq acc (mark_borrowed paths occ))
    ienv UF.empty

let mark_implicit_borrow_memory_address = function
  | MatchSingle (paths, loc, _) ->
      mark_implicit_borrow_memory_address_paths paths
        { loc; reason = DirectUse }
  (* it's still a tuple - we own it and nothing to do here *)
  | MatchTuple _ -> UF.empty

let mark_maybe_unique paths maybe_unique =
  let mark_one path =
    UF.singleton path (SharedUnique (MaybeUnique [ maybe_unique ]))
  in
  UF.pars (List.map (fun path -> mark_one path) paths)

(* the borrowing of an expression is described as a map from Uid (identifying
   borrowing binders) to UsageForest (describing the borrowing usage registerd
   to that binder). *)
module BorrowBindings = struct
  type t = UF.t Uid.Map.t

  let empty = Uid.Map.empty

  let merge f a b =
    Uid.Map.merge (fun _ a b ->
      match a, b with
      | None, None -> None
      | None, Some b -> Some b
      | Some a, None -> Some a
      | Some a, Some b -> Some (f a b)
      ) a b

  let seq = merge UF.seq
  let par = merge UF.par

  let _seqs l = List.fold_left seq empty l
  let _pars l = List.fold_left par empty l
end

module BB = BorrowBindings

let seq (uf0, bb0) (uf1, bb1) = UF.seq uf0 uf1, BB.seq bb0 bb1
let par (uf0, bb0) (uf1, bb1) = UF.par uf0 uf1, BB.par bb0 bb1

let empty  = (UF.empty, BB.empty)
let seqs = List.fold_left seq empty
let pars = List.fold_left par empty

(** returns:
    the updated value.
    the new introduced bindings.
    usage during the process *)
let pattern_match_var ~loc id value =
  match value with
  | MatchSingle (paths, _, _) -> (value, Ienv.singleton id paths, UF.empty)
  | MatchTuple values ->
      let path = UF.Path.fresh_root_of_id id in
      let ienv = Ienv.singleton id [ path ] in
      (* Mark all ps as seen, as we bind the tuple to a variable. *)
      (* Can we make it aliases instead of used? Hard to do if we want
         to preserve the tree-ness *)
      ( MatchSingle ([ path ], loc, None),
        ienv,
        UF.pars
          (List.map
             (fun (paths, loc', modes) ->
               match modes with
               | None -> UF.empty
               | Some modes ->
                   let occ =
                     { Occurrence.loc = loc'; reason = MatchTupleWithVar loc }
                   in
                   let maybe_unique = (modes, occ) in
                   mark_maybe_unique paths maybe_unique)
             values) )

(** handling pattern match of value against pat, returns ienv and uf.
    ienv is the new bindings introduced; uf is the usage caused by
    the pattern matching *)
let rec pattern_match pat value =
  match pat.pat_desc with
  | Tpat_any -> (UF.empty, Ienv.empty)
  | Tpat_var (id, _, _) ->
      let _, ienv, uf = pattern_match_var ~loc:pat.pat_loc id value in
      (uf, ienv)
  | Tpat_alias (pat', id, _, _) ->
      let value, ienv0, uf0 = pattern_match_var ~loc:pat.pat_loc id value in
      let uf1, ienv1 = pattern_match pat' value in
      (UF.seq uf0 uf1, Ienv.seq ienv0 ienv1)
  | Tpat_constant _ -> (mark_implicit_borrow_memory_address value, Ienv.empty)
  | Tpat_tuple pats ->
      pat_proj
        ~handle_tuple:(fun values ->
          (* We matched a tuple against a tuple parent and descend into each
             case *)
          (* no borrowing needed - we own the tuple! *)
          let ufs, ienvs =
            List.split
              (List.map2
                 (fun pat value -> pattern_match pat (MatchSingle value))
                 pats values)
          in
          (UF.seqs ufs, Ienv.seqs ienvs))
        ~extract_pat:Fun.id
        ~mk_proj:(fun i _ -> UsageTree.Projection.Tuple_field i)
        value pats
  | Tpat_construct (lbl, _, pats, _) ->
      pat_proj ~extract_pat:Fun.id
        ~mk_proj:(fun i _ ->
          UsageTree.Projection.Construct_field (Longident.last lbl.txt, i))
        value pats
  | Tpat_variant (lbl, mpat, _) ->
      let uf = mark_implicit_borrow_memory_address value in
      let t =
        match value with
        | MatchSingle (paths, _, modes) ->
            ( UF.Path.child_of_many paths
                (UsageTree.Projection.Variant_field lbl),
              pat.pat_loc,
              modes )
        | MatchTuple _ ->
            (* matching a tuple against variant can't pass type checking *)
            assert false
      in
      let uf', ienv =
        match mpat with
        | Some pat' -> pattern_match pat' (MatchSingle t)
        | None -> (UF.empty, Ienv.empty)
      in
      (UF.seq uf uf', ienv)
  | Tpat_record (pats, _) ->
      pat_proj
        ~extract_pat:(fun (_, _, pat) -> pat)
        ~mk_proj:(fun _ (_, l, _) ->
          UsageTree.Projection.Record_field l.lbl_name)
        value pats
  | Tpat_array (_, pats) -> (
      match value with
      | MatchTuple _ -> assert false
      | MatchSingle (paths, loc, _) ->
          let occ = { Occurrence.loc; reason = DirectUse } in
          let uf = mark_implicit_borrow_memory_address_paths paths occ in
          let ufs, ienvs =
            List.split
              (List.map
                 (fun pat ->
                   let value =
                     MatchSingle
                       ([ UF.Path.fresh_root "array_field" ], loc, None)
                   in
                   pattern_match pat value)
                 pats)
          in
          (UF.seqs (uf :: ufs), Ienv.seqs ienvs))
  | Tpat_lazy pat' -> pattern_match pat' value
  | Tpat_or (a, b, _) ->
      let uf0, ienv0 = pattern_match a value in
      let uf1, ienv1 = pattern_match b value in
      (* note that we use Ienv.par *)
      (UF.seq uf0 uf1, Ienv.par ienv0 ienv1)

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
  | MatchSingle (paths, loc, _) ->
      let occ = { Occurrence.loc; reason = DirectUse } in
      let uf = mark_implicit_borrow_memory_address_paths paths occ in
      let ufs, ienvs =
        List.split
          (List.mapi
             (fun i patlike ->
               let proj = mk_proj i patlike in
               let paths = UF.Path.child_of_many paths proj in
               let t = (paths, loc, None) in
               pattern_match (extract_pat patlike) (MatchSingle t))
             pats)
      in
      (UF.seqs (uf :: ufs), Ienv.seqs ienvs)
  | MatchTuple values -> handle_tuple values

(* We ignore exceptions in uniqueness analysis. *)
let comp_pattern_match pat value =
  match split_pattern pat with
  | Some pat', _ -> pattern_match pat' value
  | None, _ -> (UF.empty, Ienv.empty)

let maybe_paths_of_ident ?maybe_unique ienv path =
  let force reason maybe_unique =
    let use = SharedUnique.MaybeUnique [ maybe_unique ] in
    ignore (SharedUnique.force_toplevel use reason)
  in
  match path with
  | Path.Pident id -> (
      match Ident.Map.find_opt id ienv with
      (* TODO: for better error message, we should record in ienv why some
         variables are not in it. *)
      | None ->
          Option.iter (force JustTopLevel) maybe_unique;
          None
      | Some paths -> Some paths)
  (* accessing a module, which is forced by typemod to be shared and many.
     Here we force it again just to be sure *)
  | Path.Pdot _ ->
      Option.iter (force ValueFromModClass) maybe_unique;
      None
  | Path.Papply _ -> assert false

(* TODO: replace the dirty hack.

    The following functions are dirty hack and used for modules and classes.
   Currently we treat the boundary between modules/classes and their surrounding
   environment coarsely. To be specific, all references in the modules/classes
   pointing to the environment are treated as many and shared. This translates
   to enforcement on both ends:

   - inside the module, those uses needs to be forced as many and shared

   - need a UsageForest which marks those uses as many and shared, so that the
parent expression can detect conflict if any.

   The following function returns all open variables inside a module. *)
let open_variables ienv f =
  let ll = ref [] in
  let iter =
    {
      Tast_iterator.default_iterator with
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_ident (path, _, _, _, modes) -> (
              match maybe_paths_of_ident ienv path with
              | None -> ()
              | Some paths ->
                  let occ =
                    { Occurrence.loc = e.exp_loc; reason = DirectUse }
                  in
                  let maybe_unique =
                    SharedUnique.MaybeUnique [ (modes, occ) ]
                  in
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
        (* the following force is not needed, because when UA the module/class,
           maybe_paths_of_ident will force free variables to shared, because ienv
           given to it will not include the outside variables. We nevertheless
           force it here just to be sure *)
        let shared =
          Usage.SharedUnique
            (SharedUnique.force_toplevel maybe_unique FreeVariableOfModClass)
        in
        let ufs = List.map (fun path -> UF.singleton path shared) paths in
        UF.seqs ufs)
      ll
  in
  UF.seqs ufs

(* There are two modes our algorithm will work at.

   In the first mode, we care about if the expression can be considered as alias,
   for example, we want `a.x.y` to return the alias of a.x.y in addition to the
   usage of borrowing a and a.x. Note that a.x.y is not included in the usage, and
   the caller is responsible to mark a.x.y if it is used.

   In the second mode, we don't care about if the expression can be considered as
   alias. Checking a.x.y will return the usage of borrowing a and a.x, and using
   a.x.y. This mode is used in most occasions.
*)
(* the UA algorithm only looks at exp_extra to know if borrowing *)
let maybe_borrow exp_extra =
  let l =
    List.filter_map
      (function
      | Texp_borrow bb, loc, attrs ->
          assert (List.length attrs = 0);
          Some (bb, loc)
      | _ -> None
      ) exp_extra
  in
    match l with
    | [] -> None
    | [x] -> Some x
    | _ -> assert false

let maybe_borrow_binder exp_extra =
  let l =
    List.filter_map
      (function
      | Texp_borrow_binder bb, loc, attrs ->
          assert (List.length attrs = 0);
          Some (bb, loc)
      | _ -> None
      ) exp_extra
  in
    match l with
    | [] -> None
    | [x] -> Some x
    | _ -> assert false

let use_alias ~loc = function
  | None -> UF.empty
  | Some (paths, unique_use) ->
    let occ = { Occurrence.loc; reason = DirectUse } in
    let maybe_unique = (unique_use, occ) in
    mark_maybe_unique paths maybe_unique

(* Check if the expression is borrowing, or is a borrow binder; Borrowing is
  lexically bound (as implemented in typecore.ml); However, uniqueness analysis
  doesn't know anything about that, and uses only texp_borrow /
  texp_borrow_binder to reconstruct borrowing bindings. Therefore, all
  expressions need to be checked for borrow/borrow_binder. *)
let rec uf_exp_maybe_alias (ienv : Ienv.t) {exp_desc; exp_extra; exp_loc} =
    let (uf, bb), maybe_alias =
      uf_exp_desc_maybe_alias ~loc:exp_loc ienv exp_desc
    in
    let uf, bb =
      match maybe_borrow_binder exp_extra with
      | Some (uid, _) -> begin
        (* this is a borrow binder; we find the borrow usage that was registered
           under our UID *)
        (* remove uf_bb from the map as it's now bound; not needed but feel more
           principled  *)
        (* let k = Uid.Map.find uid bb in
        Format.eprintf "found for %a: %a\n" Uid.print uid UF._print k; *)
        (UF.seq uf (Uid.Map.find uid bb), Uid.Map.remove uid bb)
      end
      | None -> (uf, bb)
    in
    match maybe_borrow exp_extra with
    | Some (uids, loc) -> begin
        (* This expression is borrowing; we register at the borrow binders, and
           pretend not using the alias *)
        let uf' =
          match maybe_alias with
          | Some (paths, _unique_use) ->
            (* we don't need unique_use in the case of borrowing - shared or
              unique we don't care *)
            let occ = {Occurrence.loc; reason = DirectUse} in
            mark_borrowed paths occ
          | None -> UF.empty
        in
        let bb =
          List.fold_left (fun bb uid ->
            Uid.Map.update uid
          (function
          | None -> Some uf'
          | Some uf -> Some (UF.seq uf uf')
          ) bb) bb uids
        in
        (uf, bb), None
      end
    | None ->
        (* The expression is not borrowing *)
        (uf, bb), maybe_alias

and uf_exp (ienv : Ienv.t) e : UF.t * BB.t =
  let (uf, bb), maybe_alias = uf_exp_maybe_alias ienv e in
  UF.seq uf (use_alias ~loc:e.exp_loc maybe_alias), bb

(* This function corresponds to the first mode.

Look at exp and see if it can be treated as alias currently only texp_ident and
texp_field (and recursively so) are treated so. return paths and modes. paths is
the list of possible memory locations. returns None if exp is not alias, which
also implies that the usage of exp is included in the returned uf. *)
and uf_exp_desc_maybe_alias ~loc ienv = function
  | Texp_ident (p, _, _, _, unique_use) -> begin
      let occ = {Occurrence.loc; reason = DirectUse} in
      let maybe_unique = (unique_use, occ) in
      match maybe_paths_of_ident ~maybe_unique ienv p with
      | None -> (empty, None)
      | Some ps -> (empty, Some (ps, unique_use))
  end
  | Texp_field (e, _, l, modes, _) -> begin
      match uf_exp_maybe_alias ienv e with
      | (uf, bb), Some (paths, _) ->
          (* accessing the field meaning borrowing the parent record's mem block.
             Note that the field itself is not borrowed or used *)
          let occ = { Occurrence.loc = e.exp_loc; reason = DirectUse } in
          let uf' = mark_implicit_borrow_memory_address_paths paths occ in
          let paths' =
            UF.Path.child_of_many paths
              (UsageTree.Projection.Record_field l.lbl_name)
          in
          ((UF.seq uf uf', bb), Some (paths', modes))
      | (uf, bb), None -> ((uf, bb), None)
        end
  (* CR-someday anlorenzen: This could also support let-bindings. *)
  | exp_desc ->
    let ufbb = uf_exp_desc ~loc ienv exp_desc in
    (ufbb, None)

(* the following function corresponds to the second mode *)
and uf_exp_desc ~loc (ienv : Ienv.t)
  : expression_desc -> (UF.t * BB.t) = function
  | Texp_ident _ as exp_desc -> begin
      match uf_exp_desc_maybe_alias ~loc ienv exp_desc with
      | (uf, bb), Some (paths, modes) ->
          let occ = { Occurrence.loc; reason = DirectUse } in
          let maybe_unique = (modes, occ) in
          UF.seq uf (mark_maybe_unique paths maybe_unique), bb
      | (uf, bb), None -> uf, bb
      end
  | Texp_constant _ -> empty
  | Texp_let (_, vbs, exp') ->
      let (uf, bb), ienv' = uf_value_bindings ienv vbs in
      let ienv = Ienv.seq ienv ienv' in
      let uf', bb' = uf_exp ienv exp' in
      UF.seq uf uf', BB.seq bb bb'
  | Texp_function { param; cases } ->
      (* `param` is only a hint not a binder;
         actual binding done in cases by Tpat_var and Tpat_alias *)
      let value = MatchSingle ([ UF.Path.fresh_root_of_id param ], loc, None) in
      let uf, bb = uf_cases ienv value cases in
      (* we are constructing a closure here, and therefore any borrowing of free
         variables in the closure is in fact using shared. *)
      let uf' =
        UF.map
          (function
            | BorrowedShared (MaybeShared _ as u) ->
                (* only implicit borrowing lifted. *)
                SharedUnique
                  (SharedUnique.Shared (BorrowedShared.extract_occurrence u))
            | _ -> Unused)
          uf
      in
      UF.par uf' uf, bb
  | Texp_apply (f, xs, _, _) ->
      let ufbb0 = uf_exp ienv f in
      let ufbb1 =
        List.map
           (fun (_, arg) ->
            match arg with
            | Arg e -> uf_exp ienv e
            | Omitted _ -> UF.empty, BB.empty)
            xs
      in
      seqs (ufbb0 :: ufbb1)
  | Texp_match (e, _, cs, _) ->
      let ufbb, value = init_value_to_match ienv e in
      let ufbb' = uf_comp_cases ienv value cs in
      seq ufbb ufbb'
  | Texp_try (e, cs) ->
      let ufbb, value = init_value_to_match ienv e in
      let ufbb' = uf_cases ienv value cs in
      (* we don't know how much of e will be run; safe to assume all of them *)
      seq ufbb ufbb'
  | Texp_tuple (es, _) -> seqs (List.map (uf_exp ienv) es)
  | Texp_construct (_, _, es, _) -> seqs (List.map (uf_exp ienv) es)
  | Texp_variant (_, None) -> UF.empty, BB.empty
  | Texp_variant (_, Some (e, _)) -> uf_exp ienv e
  | Texp_record { fields; extended_expression } -> (
      let check_fields =
        seqs
          (Array.to_list
             (Array.map
                (fun field ->
                  match field with
                  | _, Kept _ -> empty
                  | _, Overridden (_, e) -> uf_exp ienv e)
                fields))
      in
      match extended_expression with
      | None -> check_fields
      | Some exp -> (
          let ufbb0, value = uf_exp_maybe_alias ienv exp in
          match value with
          | None ->
              check_fields
              (* {exp with ...}; don't know anything about exp
                 so nothing we can do here*)
          | Some (ps, modes) ->
              (* {x with ...} *)
              let ufbbs =
                Array.map
                  (fun field ->
                    match field with
                    | l, Kept _ ->
                        let ps =
                          UF.Path.child_of_many ps
                            (UsageTree.Projection.Record_field l.lbl_name)
                        in
                        let occ = { Occurrence.loc; reason = DirectUse } in
                        let maybe_unique = (modes, occ) in
                        mark_maybe_unique ps maybe_unique, BB.empty
                    | _, Overridden (_, e) -> uf_exp ienv e)
                  fields
              in
              let ufbb1 = seqs (Array.to_list ufbbs) in
              seq ufbb0 ufbb1))
  | Texp_field _ as exp_desc ->
      let (uf, bb), maybe_alias = uf_exp_desc_maybe_alias ~loc ienv exp_desc in
      UF.seq uf (use_alias ~loc maybe_alias), bb
  | Texp_setfield (exp', _, _, _, e) -> begin
      (* setfield is understood as an opaque function which borrows the memory
         address of the record *)
      let uf, bb = uf_exp ienv e in
      match uf_exp_maybe_alias ienv exp' with
      | ufbb', None -> seq (uf, bb) ufbb'
      | (uf', bb'), Some (ps, _)->
          let occ = { Occurrence.loc; reason = DirectUse } in
          UF.seqs [ uf; uf'; mark_implicit_borrow_memory_address_paths ps occ ],
          BB.seq bb bb'
    end
  | Texp_array (_, es, _) -> seqs (List.map (uf_exp ienv) es)
  | Texp_ifthenelse (if_, then_, else_opt) ->
      (* if' is only borrowed, not used; but probably doesn't matter because of
         mode crossing *)
      let ufbb0 = uf_exp ienv if_ in
      let ufbb1 =
        match else_opt with
        | Some else_ ->
            let ufbb0 = uf_exp ienv then_ in
            let ufbb1 = uf_exp ienv else_ in
            par ufbb0 ufbb1
        | None -> uf_exp ienv then_
      in
      seq ufbb0 ufbb1
  | Texp_sequence (e0, _, e1) ->
      let ufbb0 = uf_exp ienv e0 in
      let ufbb1 = uf_exp ienv e1 in
      seq ufbb0 ufbb1
  | Texp_while { wh_cond; wh_body; _ } ->
      let ufbb0 = uf_exp ienv wh_cond in
      let ufbb1 = uf_exp ienv wh_body in
      seq ufbb0 ufbb1
  | Texp_list_comprehension { comp_body; comp_clauses } ->
      let ufbb0 = uf_exp ienv comp_body in
      let ufbb1 = uf_comprehensions ienv comp_clauses in
      seq ufbb0 ufbb1
  | Texp_array_comprehension (_, { comp_body; comp_clauses }) ->
      let ufbb0 = uf_exp ienv comp_body  in
      let ufbb1 = uf_comprehensions ienv comp_clauses in
      seq ufbb0 ufbb1
  | Texp_for { for_from; for_to; for_body; _ } ->
      let uf_bb0 = uf_exp ienv for_from in
      let uf_bb1 = uf_exp ienv for_to in
      let uf_bb2 = uf_exp ienv for_body in
      seqs [ uf_bb0; uf_bb1; uf_bb2 ]
  | Texp_send (e, _, _, _) -> uf_exp ienv e
  | Texp_new _ -> empty
  | Texp_instvar _ -> empty
  | Texp_setinstvar (_, _, _, e) -> uf_exp ienv e
  | Texp_override (_, ls) ->
      seqs (List.map (fun (_, _, e) -> uf_exp ienv e ) ls)
  | Texp_letmodule (_, _, _, mod_expr, e) ->
      let uf =
        mark_shared_open_variables ienv
          (fun iter -> iter.module_expr iter mod_expr)
          mod_expr.mod_loc
      in
      let uf', bb' = uf_exp ienv e in
      UF.seq uf uf', bb'
  | Texp_letexception (_, e) -> uf_exp ienv e
  | Texp_assert e -> uf_exp ienv e
  | Texp_lazy e -> uf_exp ienv e
  | Texp_object (cls_struc, _) ->
      (* the object (methods, values) will be type-checked by Typeclass,
         which invokes uniqueness check.*)
      let uf =
        mark_shared_open_variables ienv
        (fun iter -> iter.class_structure iter cls_struc)
        loc
      in
      uf, BB.empty
  | Texp_pack mod_expr ->
      (* the module will be type-checked by Typemod which invokes uniqueness
         analysis. *)
      let uf =
        mark_shared_open_variables ienv
        (fun iter -> iter.module_expr iter mod_expr)
        mod_expr.mod_loc
      in
      uf, BB.empty
  | Texp_letop { let_; ands; body }  ->
      let uf0 = uf_binding_op ~loc ienv let_ in
      let ufs1 =
        List.map (fun bop -> uf_binding_op ~loc ienv bop) ands
      in
      let uf2 =
        uf_cases ienv
          (MatchSingle ([ UF.Path.fresh_root "letop" ], loc, None))
          [ body ]
      in
      seqs ((uf0 :: ufs1) @ [ uf2 ])
  | Texp_unreachable -> empty
  | Texp_extension_constructor _ -> empty
  | Texp_open (open_decl, e) ->
      let uf =
        mark_shared_open_variables ienv
          (fun iter -> iter.open_declaration iter open_decl)
          open_decl.open_loc
      in
      let uf', bb' = uf_exp ienv e in
      UF.seq uf uf', bb'
  | Texp_probe { handler } -> uf_exp ienv handler
  | Texp_probe_is_enabled _ -> empty
  | Texp_exclave e -> uf_exp ienv e

(* This function generate fresh value_to_match if needed, which means you should
   only call it once for each expression, for otherwise you get distinct UF.Path
   which is wrong *)
and init_single_value_to_match ienv exp
  : (UF.t * BorrowBindings.t) * single_value_to_match =
  match uf_exp_maybe_alias ienv exp with
  | ufbb, Some (ps, pp) -> (ufbb, (ps, exp.exp_loc, Some pp))
  | ufbb, None -> (ufbb, ([ UF.Path.fresh_root "match" ], exp.exp_loc, None))


(* take typed expression, do some parsing and give init_value_to_match *)
and init_value_to_match ienv exp =
  match exp.exp_desc with
  | Texp_tuple (es, _) ->
      let ufbb, ps =
        List.split (List.map (fun e -> init_single_value_to_match ienv e) es)
      in
      (seqs ufbb, MatchTuple ps)
  | _ ->
      let ufbb, s = init_single_value_to_match ienv exp in
      (ufbb, MatchSingle s)

(* returns ienv and uf; ienv is the new bindings introduced; uf is the usage
   forest caused by the binding *)
and uf_value_bindings ienv vbs =
  (* we imitate how data are accessed at runtime *)
  let ufbb, ienvs =
    List.split
      (List.map
         (fun vb ->
           let (uf, bb), value = init_value_to_match ienv vb.vb_expr in
           let uf', ienv = pattern_match vb.vb_pat value in
           ((UF.seq uf uf', bb), ienv))
         vbs)
  in
  ( seqs ufbb, Ienv.seqs ienvs)

(* type signature needed because high-ranked *)
and uf_cases_ :
      'a.
      ('a Typedtree.general_pattern -> value_to_match -> UF.t * Ienv.t) ->
      Ienv.t ->
      value_to_match ->
      'a case list ->
      UF.t * BB.t =
 fun ptm ienv value cases ->
  (* In the following we imitate how data are accessed at runtime for cases *)
  (* we first evaluate all LHS including all the guards *)
  let ufbbs0, ienvs =
    List.split
      (List.map
         (fun case ->
           let uf, ienv' = ptm case.c_lhs value in
           let (uf', bb') =
             match case.c_guard with
             | None -> empty
             | Some g ->
                 uf_exp (Ienv.seq ienv ienv') g
           in
           ((UF.seq uf uf', bb'), ienv'))
         cases)
  in
  (* we then evaluate all RHS *)
  let ufbbs1 =
    List.map2
      (fun ienv' case -> uf_exp (Ienv.seq ienv ienv') case.c_rhs)
      ienvs cases
  in
  (* now combine them - LHS is combined in sequence, RHS is combined in
     parallel *)
  seq (seqs ufbbs0) (pars ufbbs1)

and uf_cases ienv value cases  =
  uf_cases_ pattern_match ienv value cases

and uf_comp_cases ienv value cases  =
  uf_cases_ comp_pattern_match ienv value cases

and uf_comprehensions ienv cs =
  seqs
    (List.map
       (fun c ->
         match c with
         | Texp_comp_when e -> uf_exp ienv e
         | Texp_comp_for cbs ->
             seqs
               (List.map
                  (fun cb ->
                    match cb.comp_cb_iterator with
                    | Texp_comp_range { start; stop; _ } ->
                        let ufbb0 = uf_exp ienv start in
                        let ufbb1 = uf_exp ienv stop in
                        seq ufbb0 ufbb1
                    | Texp_comp_in { sequence; _ } ->
                        uf_exp ienv sequence )
                  cbs))
       cs)

and uf_binding_op ~loc ienv bo =
  let uf0 =
    match maybe_paths_of_ident ienv bo.bop_op_path with
    | Some paths ->
        let occ = { Occurrence.loc; reason = DirectUse } in
        let maybe_unique = ((Uniqueness.shared, Linearity.many), occ) in
        mark_maybe_unique paths maybe_unique
    | None -> UF.empty
  in
  let uf1, bb = uf_exp ienv bo.bop_exp in
  UF.seq uf0 uf1, bb

let check_exp exp =
  let _ = uf_exp Ienv.empty exp in
  ()

let check_value_bindings vbs =
  let _ = uf_value_bindings Ienv.empty vbs in
  ()

let report_error = function
  | UsageTree.MultiUse { here; there; error; there_is_of_here; path } ->
      let why_cannot_use_twice =
        match error with
        | `Uniqueness -> "This is used uniquely here"
        | `Linearity -> "This is defined as once"
      in
      let there_reason =
        match there.reason with
        | DirectUse -> Format.dprintf ""
        | MatchTupleWithVar _loc' ->
            Format.dprintf "which is in a tuple matched against a variable"
      in
      let relation =
        let path = Format.asprintf "%a" UsageTree.Path.human_readable path in
        if String.length path = 0 then Format.dprintf ""
        else
          match there_is_of_here with
          | Ancestor ->
              Format.dprintf "The former is %s which is the latter" path
          | Descendant ->
              Format.dprintf "The latter is %s which is the former" path
      in
      let sub = [ Location.msg ~loc:there.loc "%t%t" there_reason relation ] in
      let here_reason =
        match here.reason with
        | DirectUse -> ""
        | MatchTupleWithVar _ -> "It is in a tuple matched against a variable."
      in
      Location.errorf ~loc:here.loc ~sub
        "@[%s so cannot be used twice. %s Another use is @]"
        why_cannot_use_twice here_reason
  | SharedUnique.TopLevel { occ; error; reason } ->
      let reason =
        match reason with
        | ValueFromModClass -> "a value from a module or class"
        | FreeVariableOfModClass ->
            "a value outside the current module or class"
        | JustTopLevel -> "a value that is top-level"
      in
      let error =
        match error with
        | `Uniqueness -> "used as unique"
        | `Linearity -> "defined as once"
      in
      Location.errorf ~loc:occ.loc "@[This value is %s but it is %s@]" error
        reason
  | _ -> assert false

let report_error err =
  Printtyp.wrap_printing_env ~error:true Env.empty (fun () -> report_error err)

let () =
  Location.register_error_of_exn (function
    | (UsageTree.MultiUse _ | SharedUnique.TopLevel _) as e ->
        Some (report_error e)
    | _ -> None)
