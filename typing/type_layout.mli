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

(* CR ccasinghino: Perhaps we should take an approach similar to the new
   type_expr style, making layouts abstract to enforce the use of repr *)

type t = Types.layout

(* The functions in Constant are used after typechecking, including checking
   against module signatures.  At this point, any remaining sort variables
   may be freely defaulted. *)
module Const : sig
  type t =
    | Any
    | Value
    | Immediate64
    | Immediate
    | Void

  val constrain_default_void : Types.layout -> t
  val can_make_void : Types.layout -> bool
  (* CJC XXX at the moment we default to void whenever we can.  But perhaps it
     would be better to default to value before we actually ship. *)
end

module Violation : sig
  type nonrec t =
    | Not_a_sublayout of t * t
    | No_intersection of t * t

  val report_with_offender :
    offender:(Format.formatter -> unit) -> Format.formatter -> t -> unit
  val report_with_offender_sort :
    offender:(Format.formatter -> unit) -> Format.formatter -> t -> unit
  val report_with_name : name:string -> Format.formatter -> t -> unit
end

val sort_var : unit -> Types.sort

val any : t
val any_sort : unit -> t
val value : t
val immediate : t
val immediate64 : t
val void : t

val repr : t -> t
val default_to_value : t -> unit

(** [equal t1 t2] checks if the two layouts are equal, and will set sort
    variables to make this true if possible. (e.g., [equal (Sort 'k) (Sort
    Value)] is true and has the effect of setting 'k to value). *)
val equal : t -> t -> bool
val intersection : t -> t -> (t, Violation.t) Result.t

(** [sublayout t1 t2] returns [Ok t1] iff [t1] is a sublayout of
    of [t2].  The current hierarchy is:

    Any > Sort Value > Immediate64 > Immediate
    Any > Sort Void

    Return [Error _] if the coercion is not possible. We return a layout in the
    success case because in some cases it saves time / is convenient to have the
    same return type as intersection. *)
val sublayout : t -> t -> (t, Violation.t) result

(** Translate a user layout annotation to a layout *)
val of_layout_annotation :
  Builtin_attributes.layout_annotation option -> default:t -> t

(** Find a layout in attributes, defaulting to ~default *)
val of_attributes : default:t -> Parsetree.attributes -> t

(** Returns the sort corresponding to the layout.  Call only on representable
    layouts - errors on Any. *)
val sort_of_layout : t -> Types.sort

(* (** The least layout that represents the kind *)
 * val of_kind : Types.type_kind -> t *)

val layout_bound_of_kind : Types.type_kind -> t


(** Pretty printing *)
val to_string : t -> string
val format : Format.formatter -> t -> unit

(** Eliminate sort vars (by defaulting to value) - used in Ctype.reify *)
val reify : t -> unit
