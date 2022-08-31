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

(* Modes *)

open Types

module Locality : sig
  type const = Types.locality = Global | Local
  val min_const : const
  val max_const : const
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
  val of_const : const -> locality mode

  type t = Types.locality Types.mode
  val global : t
  val local : t
  val submode : t -> t -> (unit, unit) result
  val equate : t -> t -> (unit, unit) result
  val join : t list -> t
  val constrain_upper : t -> const
  val constrain_lower : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool
  val print : Format.formatter -> t -> unit
end

module Uniqueness : sig
  type const = Types.uniqueness = Unique | Shared
  val min_const : const
  val max_const : const
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
  val of_const : const -> uniqueness mode

  type t = Types.uniqueness Types.mode
  val unique : t
  val shared : t
  val submode : t -> t -> (unit, unit) result
  val equate : t -> t -> (unit, unit) result
  val join : t list -> t
  val constrain_upper : t -> const
  val constrain_lower : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool
  val print : Format.formatter -> t -> unit
end

module Alloc : sig

  type t = Types.alloc_mode
  (* Modes are ordered so that [global] is a submode of [local] *)
  type locality = Types.locality = Global | Local
  (* Modes are ordered so that [unique] is a submode of [shared] *)
  type uniqueness = Types.uniqueness = Unique | Shared
  type const = locality * uniqueness

  val global : t

  val local : t

  val unique : t

  val local_unique : t

  val of_const : const -> t

  val min_mode : t

  val max_mode : t

  type error = [`Locality | `Uniqueness]

  val submode : t -> t -> (unit, error) result

  val submode_exn : t -> t -> unit

  val equate : t -> t -> (unit, error) result

  val join_const : const -> const -> const

  val join : t list -> t

  (* Force a mode variable to its upper bound *)
  val constrain_upper : t -> const

  (* Force a mode variable to its lower bound *)
  val constrain_lower : t -> const

  (* Force a mode variable as shared and global *)
  val constrain_global_shared : t -> const

  val newvar : unit -> t

  val newvar_below : t -> t * bool

  val newvar_above : t -> t * bool

  val of_uniqueness : Uniqueness.t -> t

  val of_locality : Locality.t -> t

  val check_const : t -> locality option * uniqueness option

  val print : Format.formatter -> t -> unit

end

module Value : sig

  (* Modes are ordered so that [unique] is a submode of [shared] *)
  type uniqueness = Types.uniqueness = Unique | Shared

  (* Modes are ordered so that [global] is a submode of [local] *)
  type locality =
   | Global
   | Regional
   | Local

  type const = locality * uniqueness

  type t = Types.value_mode

  val global : t

  val regional : t

  val local : t

  val global_unique : t

  val regional_unique : t

  val local_unique : t

  val of_const : const -> t

  val max_mode : t

  val min_mode : t

  (** Injections from Locality and Uniqueness into [Value_mode.t] *)

  (* The 'of_*_min' functions extend the min_mode,
     the 'of_*_max' functions extend the max_mode *)
  val of_uniqueness_min : Types.uniqueness Types.mode -> t
  val of_uniqueness_max : Types.uniqueness Types.mode -> t
  val of_locality_min : Types.locality Types.mode -> t
  val of_locality_max : Types.locality Types.mode -> t

  (** Injections from [Alloc.t] into [Value_mode.t] *)

  (** [of_alloc] maps [Global] to [Global] and [Local] to [Local] *)
  val of_alloc : Alloc.t -> t

  (** Kernel operators *)

  (** The kernel operator [local_to_regional] maps [Local] to
      [Regional] and leaves the others unchanged. *)
  val local_to_regional : t -> t

  (** The kernel operator [regional_to_global] maps [Regional]
      to [Global] and leaves the others unchanged. *)
  val regional_to_global : t -> t

  val to_global : t -> t

  val to_unique : t -> t

  (** Closure operators *)

  (** The closure operator [regional_to_local] maps [Regional]
      to [Local] and leaves the others unchanged. *)
  val regional_to_local : t -> t

  (** The closure operator [global_to_regional] maps [Global] to
      [Regional] and leaves the others unchanged. *)
  val global_to_regional : t -> t

  val to_local : t -> t

  val to_shared : t -> t

  (** Note that the kernal and closure operators are in the following
      adjunction relationship:
      {v
        local_to_regional
        -| regional_to_local
        -| regional_to_global
        -| global_to_regional
      v}

      Equivalently,
      {v
        local_to_regional a <= b  iff  a <= regional_to_local b
        regional_to_local a <= b  iff  a <= regional_to_global b
        regional_to_global a <= b  iff  a <= global_to_regional b
      v}

      As well as:
      {v
        to_global -| to_local
        to_unique -| to_shared
      v}
   *)

  (** Versions of the operators that return [Alloc.t] *)

  (** Maps [Regional] to [Global] and leaves the others unchanged. *)
  val regional_to_global_alloc : t -> Alloc.t

  (** Maps [Regional] to [Local] and leaves the others unchanged. *)
  val regional_to_local_alloc : t -> Alloc.t

  (** Maps [Regional] to [Global] *)
  val regional_to_global_locality : t -> Types.locality Types.mode

  (** Maps [Regional] to [Local] *)
  val regional_to_local_locality : t -> Types.locality Types.mode

  type error = [`Regionality | `Locality | `Uniqueness]

  val submode : t -> t -> (unit, error) result

  val submode_exn : t -> t -> unit

  val submode_meet : t -> t list -> (unit, error) result

  val join : t list -> t

  val constrain_upper : t -> const

  val constrain_lower : t -> const

  val newvar : unit -> t

  val newvar_below : t -> t * bool

  val newvar_above : t -> t * bool

  val check_const : t -> locality option * uniqueness option

  val print : Format.formatter -> t -> unit

end
