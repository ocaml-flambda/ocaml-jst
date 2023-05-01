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
include
  module type of Modes
    with type 'a var = 'a Modes.var
     and type 'a mode = 'a Modes.mode
     and type ('loc, 'u, 'lin) modes = ('loc, 'u, 'lin) Modes.modes

module Locality : sig
  include module type of Modes.Locality with type const = Modes.Locality.const

  type t = Modes.Locality.t

  val min_const : const
  val max_const : const
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
  val legacy : t
  val of_const : const -> t
  val global : t
  val local : t
  val submode : t -> t -> (unit, unit) result
  val submode_exn : t -> t -> unit
  val equate : t -> t -> (unit, unit) result
  val join : t list -> t
  val constrain_upper : t -> const
  val constrain_lower : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool
  val check_const : t -> const option
  val print' : ?verbose:bool -> ?label:string -> Format.formatter -> t -> unit
  val print : Format.formatter -> t -> unit
end

module Uniqueness : sig
  include
    module type of Modes.Uniqueness with type const = Modes.Uniqueness.const

  type t = Modes.Uniqueness.t

  val legacy : t
  val min_const : const
  val max_const : const
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
  val of_const : const -> t
  val unique : t
  val shared : t
  val submode : t -> t -> (unit, unit) result
  val submode_exn : t -> t -> unit
  val equate : t -> t -> (unit, unit) result
  val join : t list -> t
  val meet : t list -> t
  val constrain_upper : t -> const
  val constrain_lower : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool
  val check_const : t -> const option
  val print' : ?verbose:bool -> ?label:string -> Format.formatter -> t -> unit
  val print : Format.formatter -> t -> unit
end

module Linearity : sig
  include module type of Modes.Linearity with type const = Modes.Linearity.const

  type t = Modes.Linearity.t

  val min_const : const
  val max_const : const
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
  val of_const : const -> t
  val to_dconst : const -> Uniqueness.const
  val from_dconst : Uniqueness.const -> const
  val to_dual : t -> Uniqueness.t
  val from_dual : Uniqueness.t -> t
  val once : t
  val many : t
  val submode : t -> t -> (unit, unit) result
  val submode_exn : t -> t -> unit
  val equate : t -> t -> (unit, unit) result
  val join : t list -> t
  val constrain_upper : t -> const
  val constrain_lower : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool
  val check_const : t -> const option
  val print' : ?verbose:bool -> ?label:string -> Format.formatter -> t -> unit
  val print : Format.formatter -> t -> unit
end

module Alloc : sig
  include module type of Modes.Alloc with type const = Modes.Alloc.const

  type t = Modes.Alloc.t

  (* Modes are ordered so that [global] is a submode of [local] *)
  (* Modes are ordered so that [unique] is a submode of [shared] *)
  val legacy : t
  val local : t
  val unique : t
  val local_unique : t

  (* val unique : const

     val local_unique : t *)

  val of_const : const -> t
  val is_const : t -> bool
  val min_mode : t
  val max_mode : t

  type error = [ `Locality | `Uniqueness | `Linearity ]

  val submode : t -> t -> (unit, error) result
  val submode_exn : t -> t -> unit
  val equate : t -> t -> (unit, error) result
  val join_const : const -> const -> const
  val join : t list -> t

  (* Force a mode variable to its upper bound *)
  val constrain_upper : t -> const

  (* Force a mode variable to its lower bound *)
  val constrain_lower : t -> const

  (* Force a mode variable to legacys *)
  val constrain_legacy : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool
  val with_locality : Locality.t -> t -> t
  val with_uniqueness : Uniqueness.t -> t -> t
  val with_linearity : Linearity.t -> t -> t
  val of_uniqueness : Uniqueness.t -> t
  val of_locality : Locality.t -> t
  val of_linearity : Linearity.t -> t

  val check_const :
    t ->
    ( Locality.const option,
      Uniqueness.const option,
      Linearity.const option )
    Modes.modes

  val print' : ?verbose:bool -> Format.formatter -> t -> unit
  val print : Format.formatter -> t -> unit
end

module Regionality : sig
  include
    module type of Modes.Regionality
      with type const = Modes.Regionality.const
       and type t = Modes.Regionality.t

  type error = [ `Regionality | `Locality ]

  val global : t
  val regional : t
  val local : t
  val submode : t -> t -> (unit, error) result
  val of_locality : Locality.t -> t
  val print : Format.formatter -> t -> unit
end

module Value : sig
  include
    module type of Modes.Value
      with type const = Modes.Value.const
       and type t = Modes.Value.t

  val legacy : t
  val regional : t
  val local : t
  val unique : t
  val regional_unique : t
  val local_unique : t
  val of_const : const -> t
  val max_mode : t
  val min_mode : t

  (** Injections from Locality and Uniqueness into [Value_mode.t] *)

  (* The 'of_*_min' functions extend the min_mode,
     the 'of_*_max' functions extend the max_mode *)
  val min_with_uniqueness : Uniqueness.t -> t
  val max_with_uniqueness : Uniqueness.t -> t
  val min_with_locality : Locality.t -> t
  val max_with_locality : Locality.t -> t
  val with_locality : Regionality.t -> t -> t
  val with_uniqueness : Uniqueness.t -> t -> t
  val with_linearity : Linearity.t -> t -> t

  (** Injections from [Alloc.t] into [Value_mode.t] *)

  val of_alloc : Alloc.t -> t
  (** [of_alloc] maps [Global] to [Global] and [Local] to [Local] *)

  (** Kernel operators *)

  val local_to_regional : t -> t
  (** The kernel operator [local_to_regional] maps [Local] to
      [Regional] and leaves the others unchanged. *)

  val regional_to_global : t -> t
  (** The kernel operator [regional_to_global] maps [Regional]
      to [Global] and leaves the others unchanged. *)

  val to_global : t -> t
  val to_unique : t -> t
  val to_once : t -> t

  (** Closure operators *)

  val regional_to_local : t -> t
  (** The closure operator [regional_to_local] maps [Regional]
      to [Local] and leaves the others unchanged. *)

  val global_to_regional : t -> t
  (** The closure operator [global_to_regional] maps [Global] to
      [Regional] and leaves the others unchanged. *)

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

  val regional_to_global_alloc : t -> Alloc.t
  (** Maps [Regional] to [Global] and leaves the others unchanged. *)

  val regional_to_local_alloc : t -> Alloc.t
  (** Maps [Regional] to [Local] and leaves the others unchanged. *)

  val regional_to_global_locality : t -> Locality.t
  (** Maps [Regional] to [Global] *)

  val regional_to_local_locality : t -> Locality.t
  (** Maps [Regional] to [Local] *)

  type error = [ `Regionality | `Locality | `Uniqueness | `Linearity ]

  val submode : t -> t -> (unit, error) result
  val submode_exn : t -> t -> unit
  val equate : t -> t -> (unit, error) result
  val submode_meet : t -> t list -> (unit, error) result
  val join : t list -> t
  val constrain_upper : t -> const
  val constrain_lower : t -> const
  val newvar : unit -> t
  val newvar_below : t -> t * bool
  val newvar_above : t -> t * bool

  val check_const :
    t ->
    ( Regionality.const option,
      Uniqueness.const option,
      Linearity.const option )
    Modes.modes

  val print' : ?verbose:bool -> Format.formatter -> t -> unit
  val print : Format.formatter -> t -> unit
end
