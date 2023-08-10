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

  let mk loc = { loc }
end

let rec iter_error f = function
  | [] -> Ok ()
  | x :: xs -> ( match f x with Ok () -> iter_error f xs | Error e -> Error e)

(* raises if lists differ in length *)
let rec list_zip l0 l1 =
  match (l0, l1) with
  | [], [] -> []
  | [], _ | _, [] -> assert false
  | x0 :: l0, x1 :: l1 -> (x0, x1) :: list_zip l0 l1

module Maybe_unique : sig
  (* I put [modality] in this module, because it seems that only this module
     cares about modes stuff *)

  (** Modalities relevant to the uniqueness analysis *)
  type modality = Shared

  val modalities_of_global_flag : global_flag -> modality list
  (** Translate from generic modalities *)

  type t
  (** The type representing a usage that could be either unique or shared *)

  val extract_occurrence : t -> Occurrence.t
  (** extract an arbitrary occurrence from this usage *)

  val singleton : unique_use -> Occurrence.t -> t
  (** construct a single usage *)

  val par : t -> t -> t

  type axis = Uniqueness | Linearity

  type cannot_force = { occ : Occurrence.t; axis : axis }
  (** Describes why cannot force shared - including the failing occurrence, and
      the failing axis *)

  val mark_multi_use : t -> (unit, cannot_force) result
  (** Call this function to indicate that this is used multiple times *)

  val modalities : modality list -> t -> t
  (** Run modalities through the usage *)

  val uniqueness : t -> Uniqueness.t
  (** Returns the uniqueness represented by this usage. If this identifier is
      expected to be unique in any branch, it will return unique. If the current
      usage is forced, it will return shared. *)
end = struct
  type modality = Shared

  let modalities_of_global_flag = function
    | Unrestricted -> []
    | Nonlocal -> [ Shared ]
    | Global -> [ Shared ]

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
  let uniqueness l = Uniqueness.meet (List.map (fun ((uniq, _), _) -> uniq) l)

  type axis = Uniqueness | Linearity
  type cannot_force = { occ : Occurrence.t; axis : axis }

  let mark_multi_use l =
    let force_one ((uni, lin), occ) =
      (* values being multi-used means two things:
         - the expected mode must be higher than [shared]
         - the access mode must be lower than [many] *)
      match Linearity.submode lin Linearity.many with
      | Error () -> Error { occ; axis = Linearity }
      | Ok () -> (
          match Uniqueness.submode Uniqueness.shared uni with
          | Ok () -> Ok ()
          | Error () -> Error { occ; axis = Uniqueness })
    in
    iter_error force_one l

  (* Note that modalities makes usages less likely to emit errors, which means
     this is to improve completeness *)
  let modality = function
    | Shared ->
        List.map (fun ((_, lin), occ) -> ((Uniqueness.shared, lin), occ))

  let modalities l u = List.fold_left (fun acc m -> modality m acc) u l
  let extract_occurrence = function [] -> assert false | (_, occ) :: _ -> occ
  let par l0 l1 = l0 @ l1
end

module Maybe_shared : sig
  type t
  type access = Read | Write

  val string_of_access : access -> string

  (** The type representing a usage that could be either shared or borrowed *)

  val extract_occurrence_access : t -> Occurrence.t * access
  (** Extract an arbitrary occurrence from the usage *)

  val add_barrier : t -> Uniqueness.t -> unit
  (** Add a barrier. The uniqueness mode represents the usage immediately
      following the current usage. If that mode is Unique, the current usage
       must be Borrowed (hence no code motion); if that mode is not restricted
       to Unique, this usage can be Borrowed or Shared (prefered). Can be called
       multiple times to represent multiple code path *)

  val par : t -> t -> t
  val singleton : unique_barrier ref -> Occurrence.t -> access -> t
end = struct
  type access = Read | Write

  let string_of_access = function Read -> "read from" | Write -> "written to"

  type t = (unique_barrier ref * Occurrence.t * access) list
  (** list of occurences together with modes to be forced as borrowed in the
  future if needed. It is a list because of multiple control flows. For
  example, if a value is used borrowed in one branch but shared in another,
  then the overall usage is shared. Therefore, the mode this list represents
  is the meet of all modes in the list. (recall that borrowed > shared).
  Therefore, if this virtual mode needs to be forced borrowed, the whole list
  needs to be forced borrowed. *)

  let par l0 l1 = l0 @ l1
  let singleton r occ access = [ (r, occ, access) ]

  let extract_occurrence_access = function
    | [] -> assert false
    | (_, occ, access) :: _ -> (occ, access)

  let add_barrier t uniq =
    List.iter (fun (barrier, _, _) -> barrier := uniq :: !barrier) t
end

module Shared : sig
  type t

  type reason =
    | Forced  (** shared because forced  *)
    | Lazy  (** shared because it is the argument of lazy forcing *)
    | Lifted of Maybe_shared.access
        (** shared because lifted from implicit borrowing, carries the original
          access *)

  val singleton : Occurrence.t -> reason -> t
  val extract_occurrence : t -> Occurrence.t
  val reason : t -> reason
end = struct
  type reason = Forced | Lazy | Lifted of Maybe_shared.access
  type t = Occurrence.t * reason

  let singleton occ reason = (occ, reason)
  let extract_occurrence (occ, _) = occ
  let reason (_, reason) = reason
end

module Usage : sig
  type t =
    | Unused  (** empty usage *)
    | Borrowed of Occurrence.t
        (** A borrowed usage with an arbitrary occurrence. The occurrence is
        only for future error messages. Currently not used, because we don't
        have explicit borrowing *)
    | Maybe_shared of Maybe_shared.t
        (** A usage that could be either borrowed or shared. *)
    | Shared of Shared.t
        (** A shared usage with an arbitrary occurrence. The occurrence is only
        for future error messages. The share_reason must corresponds to the
        occurrence *)
    | Maybe_unique of Maybe_unique.t
        (** A usage that could be either unique or shared. *)

  val extract_occurrence : t -> Occurrence.t option
  (** Extract an arbitrary occurrence from a usage *)

  type first_or_second = First | Second

  type error = {
    cannot_force : Maybe_unique.cannot_force;
    there : t;  (** The other usage  *)
    first_or_second : first_or_second;
        (** Is it the first or second usage that's failing force? *)
  }

  exception Error of error

  val seq : t -> t -> t
  (** Sequential composition *)

  val par : t -> t -> t
  (** Parallel composition  *)

  val modalities : Maybe_unique.modality list -> t -> t
  (** Run modalities through the usage *)
end = struct
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
    | Unused
    | Borrowed of Occurrence.t
    | Maybe_shared of Maybe_shared.t
    | Shared of Shared.t
    | Maybe_unique of Maybe_unique.t

  let extract_occurrence = function
    | Unused -> None
    | Borrowed occ -> Some occ
    | Maybe_shared t -> Some (Maybe_shared.extract_occurrence_access t |> fst)
    | Shared t -> Some (Shared.extract_occurrence t)
    | Maybe_unique t -> Some (Maybe_unique.extract_occurrence t)

  let par m0 m1 =
    match (m0, m1) with
    | Unused, m | m, Unused -> m
    | Borrowed _, t | t, Borrowed _ -> t
    | Maybe_shared l0, Maybe_shared l1 -> Maybe_shared (Maybe_shared.par l0 l1)
    | Maybe_shared _, t | t, Maybe_shared _ -> t
    | Shared _, t | t, Shared _ -> t
    | Maybe_unique l0, Maybe_unique l1 -> Maybe_unique (Maybe_unique.par l0 l1)

  type first_or_second = First | Second

  type error = {
    cannot_force : Maybe_unique.cannot_force;
    there : t;
    first_or_second : first_or_second;
  }

  exception Error of error

  let force_shared_multiuse t there first_or_second =
    match Maybe_unique.mark_multi_use t with
    | Ok () -> ()
    | Error cannot_force ->
        raise (Error { cannot_force; there; first_or_second })

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
        let uniq = Maybe_unique.uniqueness l1 in
        Maybe_shared.add_barrier l0 uniq;
        m1
    | Shared _, Borrowed _ -> m0
    | Maybe_unique l, Borrowed occ ->
        force_shared_multiuse l m1 First;
        Shared (Shared.singleton occ Shared.Forced)
    | Shared _, Maybe_shared _ -> m0
    | Maybe_unique l0, Maybe_shared l1 ->
        (* Four cases:
            Shared;Borrowed = Shared
            Shared;Shared = Shared
            Unique;Borrowed = Error
            Unique;Shared = Error

            As you can see, we need to force the m0 to Shared, and m1 needn't
            be constrained. The result is always Shared.
        *)
        let occ, _ = Maybe_shared.extract_occurrence_access l1 in
        force_shared_multiuse l0 m1 First;
        Shared (Shared.singleton occ Shared.Forced)
    | Shared _, Shared _ -> m0
    | Maybe_unique l, Shared _ ->
        force_shared_multiuse l m1 First;
        m1
    | Shared _, Maybe_unique l ->
        force_shared_multiuse l m0 Second;
        m0
    | Maybe_unique l0, Maybe_unique l1 ->
        force_shared_multiuse l0 m1 First;
        force_shared_multiuse l1 m0 Second;
        Shared
          (Shared.singleton (Maybe_unique.extract_occurrence l0) Shared.Forced)

  let modalities l = function
    | Maybe_unique m -> Maybe_unique (Maybe_unique.modalities l m)
    | m -> m
end

(** lifting module Usage to trees *)
module Usage_tree : sig
  module Projection : sig
    (** Projections from parent to child. *)
    type t =
      | Tuple_field of int
      | Record_field of string * Maybe_unique.modality list
      | Construct_field of string * int * Maybe_unique.modality list
      | Variant_field of label
      | Memory_address
  end

  module Path : sig
    type t
    (** Represents a path from the root to a node in a tree *)

    val child : Projection.t -> t -> t
    (** Constructing a child path *)

    val root : t
    (** The path representing the root node *)
  end

  type t
  (** Usage tree, lifted from [Usage.t] *)

  (** The relation between two nodes in a tree. Obviously the list must be
non-empty *)
  type relation =
    | Self
    | Ancestor of Projection.t list
    | Descendant of Projection.t list

  type error = {
    inner : Usage.error;  (** Describes the error concerning the two usages  *)
    first_is_of_second : relation;
        (** The relation between the two usages in the tree  *)
  }

  exception Error of error

  val seq : t -> t -> t
  (** Sequential composition lifted from [Usage.seq] *)

  val par : t -> t -> t
  (** Parallel composition lifted from [Usage.par] *)

  val singleton : Usage.t -> Path.t -> t
  (** A singleton tree containing only one leaf *)

  val mapi : (Path.t -> Usage.t -> Usage.t) -> t -> t
  (** Runs a function through the tree; the function must be monotone *)
end = struct
  module Projection = struct
    module T = struct
      type t =
        | Tuple_field of int
        | Record_field of string * Maybe_unique.modality list
        | Construct_field of string * int * Maybe_unique.modality list
        | Variant_field of label
        | Memory_address

      let compare t1 t2 =
        match (t1, t2) with
        | Tuple_field i, Tuple_field j -> Int.compare i j
        | Record_field (l1, _), Record_field (l2, _) -> String.compare l1 l2
        | Construct_field (l1, i, _), Construct_field (l2, j, _) -> (
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

  type relation =
    | Self
    | Ancestor of Projection.t list
    | Descendant of Projection.t list

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

  type error = { inner : Usage.error; first_is_of_second : relation }

  exception Error of error

  module Path = struct
    type t = Projection.t list

    let child (a : Projection.t) (p : t) : t = p @ [ a ]
    let root : t = []
  end

  let mapi_aux projs f t =
    let rec loop projs t =
      let usage = f projs t.usage in
      let children =
        Projection.Map.mapi (fun proj t -> loop (proj :: projs) t) t.children
      in
      { usage; children }
    in
    loop projs t

  let mapi f t = mapi_aux [] f t

  (* How modalities work in trees?
     For example, say we have [type r = {global_ x : string}].

     - It is possible that a node [n] of [r] has a [x]-child, in which case
     the projection must have the proper modalities set. And the usage on the
     [x]-node is taken literally without applying modalities. In particular, [n]
     and [x] could both be unique (I don't see why not).

     - It is possible that a node [n] of [r] doesn't have a [x]-child, in which
     case the usage of [x] is understood to be the usage of [n] but applied the
     [global_] modality. Note that by looking at the node [n] alone we don't have
     the modality info about its implicit usage of [n.x]. This is only discovered
     when [n] interact with another tree with [x]-child by [seq] or [par].
     However, that's also the only time when the modality matters, so it should
     be fine.
  *)
  let implicit_child = function
    | Projection.Record_field (_, modalities) -> Usage.modalities modalities
    | Projection.Construct_field (_, _, modalities) ->
        Usage.modalities modalities
    | _ -> Fun.id

  let rec mapi2 f t0 t1 =
    let usage = f Self t0.usage t1.usage in
    let children =
      Projection.Map.merge
        (fun proj c0 c1 ->
          match (c0, c1) with
          | None, None -> assert false
          | None, Some c1 ->
              let t0_usage = implicit_child proj t0.usage in
              Some
                (mapi_aux [ proj ]
                   (fun projs r -> f (Ancestor projs) t0_usage r)
                   c1)
          | Some c0, None ->
              let t1_usage = implicit_child proj t1.usage in
              Some
                (mapi_aux [ proj ]
                   (fun projs l -> f (Descendant projs) l t1_usage)
                   c0)
          | Some c0, Some c1 -> Some (mapi2 f c0 c1))
        t0.children t1.children
    in
    { usage; children }

  let par t0 t1 = mapi2 (fun _ -> Usage.par) t0 t1

  let seq t0 t1 =
    mapi2
      (fun first_is_of_second t0 t1 ->
        try Usage.seq t0 t1
        with Usage.Error error ->
          raise (Error { inner = error; first_is_of_second }))
      t0 t1

  let rec singleton leaf = function
    | [] -> { usage = leaf; children = Projection.Map.empty }
    | proj :: path ->
        {
          usage = Unused;
          children = Projection.Map.singleton proj (singleton leaf path);
        }
end

(** Lift Usage_tree to forest *)
module Usage_forest : sig
  module Path : sig
    type t

    val child : Usage_tree.Projection.t -> t -> t
    (** Construct a child path from a parent  *)

    val fresh_root : unit -> t
    (** Create a fresh tree in the forest *)
  end

  type t
  (** Represents a forest of usage. *)

  val seq : t -> t -> t
  (** Similar to [Usage_tree.seq] but lifted to forests *)

  val par : t -> t -> t
  (** Similar to [Usage_tree.par] but lifted to forests *)

  val concurrent : t list -> t
  (** Similar to [Usage_tree.concurrent] but lifted to forests *)

  val seqs : t list -> t
  val pars : t list -> t

  val unused : t
  (** The empty forest *)

  val singleton : Usage.t -> Path.t -> t
  (** The forest with only one usage, given by the path and the usage *)

  val map : (Usage.t -> Usage.t) -> t -> t
  (** Run a function through a forest. The function must be monotone *)
end = struct
  module Root_id = struct
    module T = struct
      (* Contains only one field but we might extend in the future *)
      type t = { id : int } [@@unboxed]

      let compare t1 t2 = t1.id - t2.id
    end

    include T
    module Map = Map.Make (T)

    let stamp = ref 0

    let fresh () =
      let id = !stamp in
      stamp := id + 1;
      { id }
  end

  type t = Usage_tree.t Root_id.Map.t

  module Path = struct
    type t = Root_id.t * Usage_tree.Path.t

    let child proj ((rootid, path) : t) : t =
      (rootid, Usage_tree.Path.child proj path)

    let fresh_root () : t = (Root_id.fresh (), Usage_tree.Path.root)
  end

  let unused = Root_id.Map.empty

  (** [f] must be monotone  *)
  let map2 f t0 t1 =
    Root_id.Map.merge
      (fun _rootid t0 t1 ->
        match (t0, t1) with
        | None, None -> assert false
        | None, Some t1 -> Some t1
        | Some t0, None -> Some t0
        | Some t0, Some t1 -> Some (f t0 t1))
      t0 t1

  let par t0 t1 = map2 Usage_tree.par t0 t1
  let seq t0 t1 = map2 Usage_tree.seq t0 t1
  let pars l = List.fold_left par unused l
  let seqs l = List.fold_left seq unused l

  (* Given our [seq] and [par], one might tend to define [concurrent] first as
     a binary operation, then generalize it to n-ary using [List.fold]. This is
     however wrong. For example, the concurrent of u0, u1, u2 is:
     pars [seqs [u0,u1,u2];
           seqs [u0,u2,u1];
           seqs [u1,u0,u2];
           seqs [u1,u2,u0];
           seqs [u2,u0,u1];
           seqs [u2,u1,u0]]
     which is different from
     concurrent (concurrent u0 u1) u2
     which does not include the possibility of [u2] between [u0] and [u1].

     In summary, the logic of [concurrent] is interwined with lists, so it's better
     to start with lists outright *)
  let rec concurrent = function
    | [] -> unused
    | t :: l ->
        let t' = concurrent l in
        par (seq t' t) (seq t t')

  let singleton leaf ((rootid, path') : Path.t) =
    Root_id.Map.singleton rootid (Usage_tree.singleton leaf path')

  (** f must be monotone *)
  let map f =
    Root_id.Map.mapi (fun _root tree ->
        Usage_tree.mapi (fun _projs usage -> f usage) tree)
end

module UF = Usage_forest

module Paths : sig
  type t
  (** Represents a list of [UF.Path.t]  *)

  val child : Usage_tree.Projection.t -> t -> t
  (** Returns the element-wise child *)

  val legacy : t
  (** Representing legacy values whose modes are managed by the type checker.
      They are ignored by uniqueness analysis and represented as empty lists *)

  val mark : Usage.t -> t -> UF.t
  val fresh : unit -> t
  val par : t -> t -> t

  val mark_implicit_borrow_memory_address :
    Maybe_shared.access -> Occurrence.t -> t -> UF.t

  val mark_shared : Occurrence.t -> Shared.reason -> t -> UF.t
end = struct
  type t = UF.Path.t list

  let par a b = a @ b
  let legacy = []
  let child proj t = List.map (UF.Path.child proj) t
  let mark usage t = UF.pars (List.map (UF.singleton usage) t)
  let fresh () = [ UF.Path.fresh_root () ]

  let mark_implicit_borrow_memory_address access occ paths =
    (* Currently we just generate a dummy unique_barrier ref that won't be
        consumed. The distinction between implicit and explicit borrowing is
        still needed because they are handled differently in closures *)
    let barrier = ref [] in
    mark
      (Maybe_shared (Maybe_shared.singleton barrier occ access))
      (child Usage_tree.Projection.Memory_address paths)

  let mark_shared occ reason paths =
    mark (Shared (Shared.singleton occ reason)) paths
end

module Value : sig
  type t
  (** See [mk] for its meaning *)

  val mk : Paths.t -> ?unique_use:unique_use -> Occurrence.t -> t
  (** A value contains the list of paths it could points to, the unique_use if
      it's a variable, and its occurrence in the source code. [unique_use] could
      be None if it's not a variable (e.g. result of an application) *)

  val fresh : ?unique_use:unique_use -> Occurrence.t -> t

  val legacy : ?unique_use:unique_use -> Occurrence.t -> t
  (** The legacy value, lifted from [Paths.legacy] *)

  val paths : t -> Paths.t
  (** Returns the paths *)

  val occ : t -> Occurrence.t
  (** Returns the occurrence  *)

  val mark_maybe_unique : t -> UF.t
  (** Mark the value as shared_or_unique   *)

  val mark_implicit_borrow_memory_address : Maybe_shared.access -> t -> UF.t
  (** Mark the memory_address of the value as implicitly borrowed
      (borrow_or_shared). We still ask for the [occ] argument, because
      [Value.occ] is the occurrence of the value, not necessary the place where
      it is borrowed. *)
end = struct
  type t = {
    paths : Paths.t;
    unique_use : unique_use option;
    occ : Occurrence.t;
  }

  let mk paths ?unique_use occ = { paths; unique_use; occ }

  let fresh ?unique_use occ =
    let paths = Paths.fresh () in
    { paths; unique_use; occ }

  let legacy = mk Paths.legacy

  let mark_implicit_borrow_memory_address access { paths; occ } =
    Paths.mark_implicit_borrow_memory_address access occ paths

  let mark_maybe_unique { paths; unique_use; occ } =
    match unique_use with
    | None ->
        (* the value is the result of some application *)
        UF.unused
    | Some unique_use ->
        Paths.mark (Maybe_unique (Maybe_unique.singleton unique_use occ)) paths

  let paths { paths; _ } = paths
  let occ { occ; _ } = occ
end

module Ienv : sig
  module Extension : sig
    type t
    (** Extention to Ienv. Usually generated by a pattern *)

    val disjunct : t -> t -> t
    (** Composition for [OR] patterns. This operation is commutative *)

    val conjunct : t -> t -> t
    (** Composition for conjunctive patterns. The two extensions must be
    disjoint. *)

    val conjuncts : t list -> t
    (** Similar to [conjunct] but lifted to lists *)

    val empty : t
    (** The empty extension *)

    val singleton : Ident.t -> Paths.t -> t
    (* Constructing a mapping with only one mapping  *)
  end

  type t
  (** Mapping from identifiers to a list of possible nodes, each represented by
      a path into the forest, instead of directly ponting to the node. *)

  val extend : t -> Extension.t -> t
  (** Extend a mapping with an extension *)

  val empty : t
  (** The empty mapping  *)

  val find_opt : Ident.t -> t -> Paths.t option
  (** Find the list of paths corresponding to an identifier  *)
end = struct
  module Extension = struct
    type t = Paths.t Ident.Map.t

    let disjunct ienv0 ienv1 =
      Ident.Map.merge
        (fun _id locs0 locs1 ->
          match (locs0, locs1) with
          | None, None -> None
          | Some paths0, Some paths1 -> Some (Paths.par paths0 paths1)
          (* cannot bind variable only in one of the OR-patterns *)
          | _, _ -> assert false)
        ienv0 ienv1

    let empty = Ident.Map.empty

    let conjunct ienv0 ienv1 =
      Ident.Map.union
        (fun _id _ _ ->
          (* cannot bind variable twice in a single pattern *)
          assert false)
        ienv0 ienv1

    let conjuncts = List.fold_left conjunct empty
    let singleton id locs = Ident.Map.singleton id locs
  end

  type t = Paths.t Ident.Map.t

  let empty = Ident.Map.empty

  let extend t ex =
    Ident.Map.union
      (* the extension shadows the original *)
        (fun _id _paths0 paths1 -> Some paths1)
      t ex

  let find_opt = Ident.Map.find_opt
end

(* The fun algebraic stuff ends. Here comes the concrete mess *)

(* Forcing due to boundary is more about OCaml than the algebra, hence defined
   here (as opposed to earlier) *)

(** See [report_error] for explanation *)
type boundary_reason =
  | Paths_from_mod_class (* currently will never trigger *)
  | Free_var_of_mod_class (* currently will never trigger *)
  | Out_of_mod_class

type boundary = {
  cannot_force : Maybe_unique.cannot_force;
  reason : boundary_reason;  (** which kind of boundary is being crossed? *)
}

exception Boundary of boundary

let force_shared_boundary t ~reason =
  match Maybe_unique.mark_multi_use t with
  | Ok () -> ()
  | Error cannot_force -> raise (Boundary { cannot_force; reason })

type value_to_match =
  | Match_tuple of Value.t list
      (** The value being matched is a tuple; we treat it specially so matching
  tuples against tuples merely create alias instead of uses; We need [Value.t]
  instead of [Paths.t] because the tuple could be bound to a variable, in which
    case all values in the tuple is considered used *)
  | Match_single of Paths.t  (** The value being matched is not a tuple *)

let conjuncts_pattern_match l =
  let exts, ufs = List.split l in
  (Ienv.Extension.conjuncts exts, UF.seqs ufs)

let rec pattern_match_tuple pat values =
  match pat.pat_desc with
  | Tpat_or (pat0, pat1, _) ->
      let ext0, uf0 = pattern_match_tuple pat0 values in
      let ext1, uf1 = pattern_match_tuple pat1 values in
      (Ienv.Extension.disjunct ext0 ext1, UF.seq uf0 uf1)
  | Tpat_tuple pats ->
      List.map2
        (fun pat value -> pattern_match_single pat (Value.paths value))
        pats values
      |> conjuncts_pattern_match
  | _ ->
      (* Mark all values in the tuple as used, because we are binding the tuple
         to a variable *)
      let uf = UF.seqs (List.map Value.mark_maybe_unique values) in
      let paths = Paths.fresh () in
      let ext, uf' = pattern_match_single pat paths in
      (ext, UF.seq uf uf')

and pattern_match_single pat paths : Ienv.Extension.t * UF.t =
  let loc = pat.pat_loc in
  let occ = Occurrence.mk loc in
  match pat.pat_desc with
  | Tpat_or (pat0, pat1, _) ->
      let ext0, uf0 = pattern_match_single pat0 paths in
      let ext1, uf1 = pattern_match_single pat1 paths in
      (Ienv.Extension.disjunct ext0 ext1, UF.seq uf0 uf1)
  | Tpat_any -> (Ienv.Extension.empty, UF.unused)
  | Tpat_var (id, _, _) -> (Ienv.Extension.singleton id paths, UF.unused)
  | Tpat_alias (pat', id, _, _) ->
      let ext0 = Ienv.Extension.singleton id paths in
      let ext1, uf = pattern_match_single pat' paths in
      (Ienv.Extension.conjunct ext0 ext1, uf)
  | Tpat_constant _ ->
      ( Ienv.Extension.empty,
        Paths.mark_implicit_borrow_memory_address Read occ paths )
  | Tpat_construct (lbl, cd, pats, _) ->
      let prologue = Paths.mark_implicit_borrow_memory_address Read occ paths in
      let pats_args = list_zip pats cd.cstr_args in
      let ext, uf =
        List.mapi
          (fun i (pat, (_, gf)) ->
            let paths =
              Paths.child
                (Usage_tree.Projection.Construct_field
                   ( Longident.last lbl.txt,
                     i,
                     Maybe_unique.modalities_of_global_flag gf ))
                paths
            in
            pattern_match_single pat paths)
          pats_args
        |> conjuncts_pattern_match
      in
      (ext, UF.seq prologue uf)
  | Tpat_variant (lbl, mpat, _) ->
      let prologue = Paths.mark_implicit_borrow_memory_address Read occ paths in
      let ext, uf =
        match mpat with
        | Some pat' ->
            let paths =
              Paths.child (Usage_tree.Projection.Variant_field lbl) paths
            in
            pattern_match_single pat' paths
        | None -> (Ienv.Extension.empty, UF.unused)
      in
      (ext, UF.seq prologue uf)
  | Tpat_record (pats, _) ->
      let prologue = Paths.mark_implicit_borrow_memory_address Read occ paths in
      let ext, uf =
        List.map
          (fun (_, l, pat) ->
            let paths =
              Paths.child
                (Usage_tree.Projection.Record_field
                   ( l.lbl_name,
                     Maybe_unique.modalities_of_global_flag l.lbl_global ))
                paths
            in
            pattern_match_single pat paths)
          pats
        |> conjuncts_pattern_match
      in
      (ext, UF.seq prologue uf)
  | Tpat_array (_, pats) ->
      let prologue = Paths.mark_implicit_borrow_memory_address Read occ paths in
      let ext, uf =
        List.map
          (fun pat ->
            let paths = Paths.fresh () in
            pattern_match_single pat paths)
          pats
        |> conjuncts_pattern_match
      in
      (ext, UF.seq prologue uf)
  | Tpat_lazy pat ->
      (* forcing a lazy expression is like calling a nullary-function *)
      let uf = Paths.mark_shared occ Lazy paths in
      let paths = Paths.fresh () in
      let ext, uf' = pattern_match_single pat paths in
      (ext, UF.seq uf uf')
  | Tpat_tuple pats ->
      let prologue = Paths.mark_implicit_borrow_memory_address Read occ paths in
      let ext, uf =
        List.mapi
          (fun i pat ->
            let paths =
              Paths.child (Usage_tree.Projection.Tuple_field i) paths
            in
            pattern_match_single pat paths)
          pats
        |> conjuncts_pattern_match
      in
      (ext, UF.seq prologue uf)

let pattern_match pat = function
  | Match_tuple values -> pattern_match_tuple pat values
  | Match_single paths -> pattern_match_single pat paths

(* We ignore exceptions in uniqueness analysis. *)
let comp_pattern_match pat value =
  match split_pattern pat with
  | Some pat', _ -> pattern_match pat' value
  | None, _ -> (Ienv.Extension.empty, UF.unused)

let maybe_paths_of_ident ?maybe_unique ienv path =
  let force reason (unique_use, occ) =
    let maybe_unique = Maybe_unique.singleton unique_use occ in
    force_shared_boundary maybe_unique ~reason
  in
  match path with
  | Path.Pident id -> (
      match Ienv.find_opt id ienv with
      (* TODO: for better error message, we should record in ienv why some
         variables are not in it. *)
      | None ->
          Option.iter (force Out_of_mod_class) maybe_unique;
          None
      | Some paths -> Some paths)
  (* accessing a module, which is forced by typemod to be shared and many.
     Here we force it again just to be sure *)
  | Path.Pdot _ ->
      Option.iter (force Paths_from_mod_class) maybe_unique;
      None
  | Path.Papply _ -> assert false

(* TODO: replace the dirty hack.
   The following functions are dirty hacks and used for modules and classes.
   Currently we treat the boundary between modules/classes and their surrounding
   environment coarsely. To be specific, all references in the modules/classes
   pointing to the environment are treated as many and shared. This translates
   to enforcement on both ends:
   - inside the module, those uses needs to be forced as many and shared
   - need a UF.t which marks those uses as many and shared, so that the
     parent expression can detect conflict if any. *)

(** Returns all open variables inside a module. *)
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
                  let occ = Occurrence.mk e.exp_loc in
                  let maybe_unique = Maybe_unique.singleton unique_use occ in
                  ll := (paths, maybe_unique) :: !ll)
          | _ -> ());
          Tast_iterator.default_iterator.expr self e);
    }
  in
  f iter;
  !ll

(** Marks all open variables in a class/module as shared,
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
        force_shared_boundary maybe_unique ~reason:Free_var_of_mod_class;
        let shared =
          Usage.Shared
            (Shared.singleton
               (Maybe_unique.extract_occurrence maybe_unique)
               Shared.Forced)
        in
        Paths.mark shared paths)
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

(** Corresponds to the second mode *)
let rec check_uniqueness_exp_ exp (ienv : Ienv.t) : UF.t =
  match exp.exp_desc with
  | Texp_ident _ -> (
      match check_uniqueness_exp' exp ienv with
      | None, uf -> uf
      | Some value, uf -> UF.seq uf (Value.mark_maybe_unique value))
  | Texp_constant _ -> UF.unused
  | Texp_let (_, vbs, exp') ->
      let ext, uf = check_uniqueness_value_bindings_ vbs ienv in
      let uf' = check_uniqueness_exp_ exp' (Ienv.extend ienv ext) in
      UF.seq uf uf'
  | Texp_function { cases; _ } ->
      (* `param` is only a hint not a binder;
         actual binding done in cases by Tpat_var and Tpat_alias *)
      let value = Match_single (Paths.fresh ()) in
      let uf = check_uniqueness_cases value cases ienv in
      (* we are constructing a closure here, and therefore any borrowing of free
         variables in the closure is in fact using shared. *)
      UF.map
        (function
          | Maybe_shared t ->
              (* implicit borrowing lifted. *)
              let occ, access = Maybe_shared.extract_occurrence_access t in
              Shared (Shared.singleton occ (Shared.Lifted access))
          | m ->
              (* other usage stays the same *)
              m)
        uf
  | Texp_apply (f, xs, _, _) ->
      let uf = check_uniqueness_exp_ f ienv in
      let ufs =
        List.map
          (fun (_, arg) ->
            match arg with
            | Arg e -> check_uniqueness_exp_ e ienv
            | Omitted _ -> UF.unused)
          xs
      in
      UF.concurrent (uf :: ufs)
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
  | Texp_variant (_, None) -> UF.unused
  | Texp_variant (_, Some (e, _)) -> check_uniqueness_exp_ e ienv
  | Texp_record { fields; extended_expression } -> (
      let check_fields =
        UF.seqs
          (Array.to_list
             (Array.map
                (fun field ->
                  match field with
                  | _, Kept _ -> UF.unused
                  | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv)
                fields))
      in
      match extended_expression with
      | None -> check_fields
      | Some exp -> (
          match check_uniqueness_exp' exp ienv with
          | None, uf ->
              UF.seq uf check_fields
              (* {exp with ...}; don't know anything about exp so nothing we can
                 do here*)
          | Some value, uf0 ->
              (* {x with ...} *)
              let prologue =
                Value.mark_implicit_borrow_memory_address Read value
              in
              let ufs =
                Array.map
                  (fun field ->
                    match field with
                    | l, Kept (_, unique_use) ->
                        let value =
                          let occ = Value.occ value in
                          let paths = Value.paths value in
                          let paths =
                            Paths.child
                              (Usage_tree.Projection.Record_field
                                 ( l.lbl_name,
                                   Maybe_unique.modalities_of_global_flag
                                     l.lbl_global ))
                              paths
                          in
                          Value.mk paths ~unique_use occ
                        in
                        Value.mark_maybe_unique value
                    | _, Overridden (_, e) -> check_uniqueness_exp_ e ienv)
                  fields
              in
              UF.seqs (uf0 :: prologue :: Array.to_list ufs)))
  | Texp_field _ -> (
      match check_uniqueness_exp' exp ienv with
      | Some value, uf -> UF.seq uf (Value.mark_maybe_unique value)
      | None, uf -> uf)
  | Texp_setfield (exp', _, _, _, e) -> (
      (* Setfield allows mutations outside of our uniqueness extension. We still
         need to track it, because a unique use (strong update) followed by
         setfield could cause segfault. Tracking it as shared/unique is also too
         strong, because setfield followed by unique use should be allowed.
         Tracking it as borrow_or_shared (which is how we track `getfield`)
         sounds about right. *)
      let uf = check_uniqueness_exp_ e ienv in
      match check_uniqueness_exp' exp' ienv with
      | None, uf' -> UF.seq uf uf'
      | Some value, uf' ->
          UF.seqs
            [ uf; uf'; Value.mark_implicit_borrow_memory_address Write value ])
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
  | Texp_new _ -> UF.unused
  | Texp_instvar _ -> UF.unused
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
  | Texp_lazy e ->
      (* We would need to lift implicit borrow to shared. However, this is not
         needed because [Texp_lazy] is already protected by [Share_lock] *)
      check_uniqueness_exp_ e ienv
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
        check_uniqueness_cases (Match_single (Paths.fresh ())) [ body ] ienv
      in
      UF.seqs ((uf0 :: ufs1) @ [ uf2 ])
  | Texp_unreachable -> UF.unused
  | Texp_extension_constructor _ -> UF.unused
  | Texp_open (open_decl, e) ->
      let uf =
        mark_shared_open_variables ienv
          (fun iter -> iter.open_declaration iter open_decl)
          open_decl.open_loc
      in
      UF.seq uf (check_uniqueness_exp_ e ienv)
  | Texp_probe { handler } -> check_uniqueness_exp_ handler ienv
  | Texp_probe_is_enabled _ -> UF.unused
  | Texp_exclave e -> check_uniqueness_exp_ e ienv

(**
Corresponds to the first mode.

Look at exp and see if it can be treated as an alias. Currently only
[Texp_ident] and [Texp_field] (and recursively so) are treated so. If it returns
[Some Value.t], the caller is responsible to mark it as used as needed *)
and check_uniqueness_exp' exp ienv : Value.t option * UF.t =
  let loc = exp.exp_loc in
  match exp.exp_desc with
  | Texp_ident (p, _, _, _, unique_use) -> (
      let occ = Occurrence.mk loc in
      let maybe_unique = (unique_use, occ) in
      match maybe_paths_of_ident ~maybe_unique ienv p with
      | None ->
          (* cross module access - don't track;
             Note the difference between [Some Value.empty] and [None]:
             - The former is for legacy access
             - The latter is for non-variable expressions *)
          (Some (Value.legacy ~unique_use occ), UF.unused)
      | Some paths -> (Some (Value.mk paths ~unique_use occ), UF.unused))
  | Texp_field (e, _, l, unique_use, _) -> (
      let value, uf = check_uniqueness_exp' e ienv in
      match value with
      | None ->
          (* (exp).field is still an expression; return None *)
          (None, uf)
      | Some value ->
          (* accessing the field meaning borrowing the parent record's mem
             block. Note that the field itself is not borrowed or used *)
          let uf' = Value.mark_implicit_borrow_memory_address Read value in
          let occ = Occurrence.mk loc in
          let paths =
            Paths.child
              (Usage_tree.Projection.Record_field
                 ( l.lbl_name,
                   Maybe_unique.modalities_of_global_flag l.lbl_global ))
              (Value.paths value)
          in
          let value = Value.mk paths ~unique_use occ in
          (Some value, UF.seq uf uf'))
  (* CR-someday anlorenzen: This could also support let-bindings. *)
  | _ -> (None, check_uniqueness_exp_ exp ienv)

and init_single_value_to_match exp ienv : Value.t * UF.t =
  match check_uniqueness_exp' exp ienv with
  | None, uf ->
      let occ = Occurrence.mk exp.exp_loc in
      (* When matching on an expression, we create fresh value, who will have
         children by being matched *)
      let value = Value.fresh occ in
      (value, uf)
  | Some value, uf -> (value, uf)

(** take typed expression, do some parsing and returns [init_value_to_match] *)
and init_value_to_match exp ienv : value_to_match * UF.t =
  match exp.exp_desc with
  | Texp_tuple (es, _) ->
      let values, ufs =
        List.split (List.map (fun e -> init_single_value_to_match e ienv) es)
      in
      (Match_tuple values, UF.seqs ufs)
  | _ ->
      let value, uf = init_single_value_to_match exp ienv in
      (Match_single (Value.paths value), uf)

(** Returns [ienv] and [uf].
   [ienv] is the new bindings introduced;
   [uf] is the usage forest caused by the binding
*)
and check_uniqueness_value_bindings_ vbs ienv =
  (* we imitate how data are accessed at runtime *)
  let exts, ufs =
    List.split
      (List.map
         (fun vb ->
           let value, uf = init_value_to_match vb.vb_expr ienv in
           let ienv, uf' = pattern_match vb.vb_pat value in
           (ienv, UF.seq uf uf'))
         vbs)
  in
  (Ienv.Extension.conjuncts exts, UF.seqs ufs)

(* type signature needed because high-ranked *)
and check_uniqueness_cases_ :
      'a.
      ('a Typedtree.general_pattern ->
      value_to_match ->
      Ienv.Extension.t * UF.t) ->
      value_to_match ->
      'a case list ->
      Ienv.t ->
      UF.t =
 fun ptm value cases ienv ->
  (* In the following we imitate how data are accessed at runtime for cases *)
  (* we first evaluate all LHS including all the guards, _sequentially_ *)
  let exts, ufs0 =
    List.split
      (List.map
         (fun case ->
           let ext, uf = ptm case.c_lhs value in
           let uf' =
             match case.c_guard with
             | None -> UF.unused
             | Some g -> check_uniqueness_exp_ g (Ienv.extend ienv ext)
           in
           (ext, UF.seq uf uf'))
         cases)
  in
  (* we then evaluate all RHS, in _parallel_ *)
  let ufs1 =
    List.map2
      (fun ext case -> check_uniqueness_exp_ case.c_rhs (Ienv.extend ienv ext))
      exts cases
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
        let occ = Occurrence.mk exp.exp_loc in
        let value = Value.mk paths occ in
        Value.mark_maybe_unique value
    | None -> UF.unused
  in
  let uf1 = check_uniqueness_exp_ bo.bop_exp ienv in
  UF.seq uf0 uf1

let check_uniqueness_exp exp =
  let _ = check_uniqueness_exp_ exp Ienv.empty in
  ()

let check_uniqueness_value_bindings vbs =
  let _ = check_uniqueness_value_bindings_ vbs Ienv.empty in
  ()

let report_multi_use
    {
      Usage_tree.inner =
        { cannot_force = { occ; axis }; there; first_or_second };
      first_is_of_second;
    } =
  let here_usage = "used" in
  let there_usage =
    match there with
    | Usage.Maybe_shared t -> (
        let _, access = Maybe_shared.extract_occurrence_access t in
        match access with Read -> "read from" | Write -> "written to")
    | Usage.Shared t -> (
        match Shared.reason t with
        | Forced | Lazy -> "used"
        | Lifted access ->
            Maybe_shared.string_of_access access
            ^ " in a closure that might be called later")
    | _ -> "used"
  in
  let first, first_usage, second, second_usage =
    match first_or_second with
    | Usage.First ->
        ( occ,
          here_usage,
          Option.get (Usage.extract_occurrence there),
          there_usage )
    | Usage.Second ->
        ( Option.get (Usage.extract_occurrence there),
          there_usage,
          occ,
          here_usage )
  in
  let first_is_of_second =
    match first_is_of_second with
    | Self
    | Ancestor [ Usage_tree.Projection.Memory_address ]
    | Descendant [ Usage_tree.Projection.Memory_address ] ->
        "it"
    | Descendant _ -> "part of it"
    | Ancestor _ -> "it is part of a value that"
  in

  (* English is sadly not very composible, we write out all four cases
     manually *)
  let error =
    match (first_or_second, axis) with
    | First, Uniqueness ->
        Format.dprintf
          "This value is %s here,@ but %s has already been %s as unique:"
          second_usage first_is_of_second first_usage
    | First, Linearity ->
        Format.dprintf
          "This value is %s here,@ but %s is defined as once and has already \
           been %s:"
          second_usage first_is_of_second first_usage
    | Second, Uniqueness ->
        Format.dprintf
          "This value is %s here as unique,@ but %s has already been %s:"
          second_usage first_is_of_second first_usage
    | Second, Linearity ->
        Format.dprintf
          "This value is defined as once and %s here,@ but %s has already been \
           %s:"
          second_usage first_is_of_second first_usage
  in
  let sub = [ Location.msg ~loc:first.loc "" ] in
  Location.errorf ~loc:second.loc ~sub "@[%t@]" error

let report_boundary { cannot_force = { occ; axis }; reason } =
  let reason =
    match reason with
    | Paths_from_mod_class -> "another module or class"
    | Free_var_of_mod_class -> "outside the current module or class"
    | Out_of_mod_class -> "outside the current module or class"
  in
  let error =
    match axis with
    | Uniqueness -> "This value is shared but used as unique"
    | Linearity -> "This value is once but used as many"
  in
  Location.errorf ~loc:occ.loc "@[%s.\nHint: This value comes from %s.@]" error
    reason

let report_multi_use err =
  Printtyp.wrap_printing_env ~error:true Env.empty (fun () ->
      report_multi_use err)

let report_boundary err =
  Printtyp.wrap_printing_env ~error:true Env.empty (fun () ->
      report_boundary err)

let () =
  Location.register_error_of_exn (function
    | Usage_tree.Error e -> Some (report_multi_use e)
    | Boundary e -> Some (report_boundary e)
    | _ -> None)
