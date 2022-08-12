(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Jeremie Dimino, Jane Street Europe                   *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t = Types.layout


module Constant : sig
  type t =
    | Any
    | Value
    | Immediate64
    | Immediate
    | Void

  val constrain_default_void : Types.layout -> t
end

module Violation : sig
  type nonrec t =
    | Not_a_sublayout of t * t
    | No_intersection of t * t

  val report_with_offender :
    offender:(Format.formatter -> unit) -> Format.formatter -> t -> unit
  val report_with_name : name:string -> Format.formatter -> t -> unit
end

val any : t
val any_sort : unit -> t
val value : t
val immediate : t
val immediate64 : t
val void : t

val equal : t -> t -> bool
val intersection : t -> t -> (t, Violation.t) Result.t

(** [sublayout t1 t2] returns [Ok ()] iff [t1] is a sublayout of
    of [t2].  The current hierarchy is:

    Any > Sort Value > Immediate64 > Immediate
    Any > Sort Void

    Return [Error _] if the coercion is not possible. *)
val sublayout : t -> t -> (unit, Violation.t) result

(** Translate a user layout annotation to a layout *)
val of_layout_annotation :
  Builtin_attributes.layout_annotation option -> default:t -> t

(** Find a layout in attributes, defaulting to ~default *)
val of_attributes : default:t -> Parsetree.attributes -> t


(* (** The least layout that represents the kind *)
 * val of_kind : Types.type_kind -> t *)

val layout_bound_of_record_representation : Types.record_representation -> t
val layout_bound_of_variant_representation : Types.variant_representation -> t
val layout_bound_of_kind : Types.type_kind -> t


(** Pretty printing *)
val to_string : t -> string

val reify : t -> unit
