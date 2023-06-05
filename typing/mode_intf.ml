open Solver_intf

module type Const = sig
  include Lattice
  val legacy : t
end

module type Common = sig
  module Const : Const

  type error
  type 'd t
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t

  val min : lr
  val max : lr
  val disallow_right : ('l * 'r) t -> ('l * disallowed) t
  val disallow_left : ('l * 'r) t -> (disallowed * 'r) t
  val allow_right : ('l * allowed) t -> ('l * 'r) t
  val allow_left : (allowed * 'r) t -> ('l * 'r) t
  val newvar : ?hint:string -> unit -> ('l * 'r) t
  val submode : (allowed * 'r) t -> ('l * allowed) t -> (unit, error) result
  val equate : lr -> lr -> (unit, error) result
  val submode_exn : (allowed * 'r) t -> ('l * allowed) t -> unit
  val equate_exn : lr -> lr -> unit
  val join : (allowed * 'r) t list -> left_only t
  val meet : ('l * allowed) t list -> right_only t
  val newvar_above : ?hint:string -> (allowed * 'r) t -> ('l * 'r_) t * bool
  val newvar_below : ?hint:string -> ('l * allowed) t -> ('l_ * 'r) t * bool

  val print :
    ?verbose:bool -> ?axis:string -> Format.formatter -> ('l * 'r) t -> unit

  val print_simple : Format.formatter -> ('l * 'r) t -> unit
  val constrain_lower : (allowed * 'r) t -> Const.t
  val constrain_upper : ('l * allowed) t -> Const.t
  val check_const : ('l * 'r) t -> Const.t option
  val of_const : Const.t -> ('l * 'r) t
  val legacy : lr
end

type ('loc, 'lin, 'uni) modes = {
  locality : 'loc;
  linearity : 'lin;
  uniqueness : 'uni;
}

module type Alloc_or_Value = sig
  module Locality : Common
  module Uniqueness : Common
  module Linearity : Common
  module Const : sig
    include Const with type t =
    (Locality.Const.t, Linearity.Const.t, Uniqueness.Const.t) modes
    val close_over : t -> t
    val partial_apply : t -> t
  end

  type error = [ `Locality | `Uniqueness | `Linearity ]

  include Common with module Const := Const and type error := error

  (* some over-riding *)
  val print : ?verbose:bool -> Format.formatter -> ('l * 'r) t -> unit

  val check_const :
    ('l * 'r) t ->
    ( Locality.Const.t option,
      Linearity.Const.t option,
      Uniqueness.Const.t option )
    modes

  val locality_of : ('l * 'r) t -> ('l * 'r) Locality.t
  val uniqueness_of : ('l * 'r) t -> ('l * 'r) Uniqueness.t
  val linearity_of : ('l * 'r) t -> ('l * 'r) Linearity.t
  val max_with_uniqueness : ('l * 'r) Uniqueness.t -> (disallowed * 'r) t
  val min_with_uniqueness : ('l * 'r) Uniqueness.t -> ('l * disallowed) t
  val min_with_locality : ('l * 'r) Locality.t -> ('l * disallowed) t
  val max_with_locality : ('l * 'r) Locality.t -> (disallowed * 'r) t
  val min_with_linearity : ('l * 'r) Linearity.t -> ('l * disallowed) t
  val max_with_linearity : ('l * 'r) Linearity.t -> (disallowed * 'r) t
  val set_locality_min : ('l * 'r) t -> ('l * disallowed) t
  val set_locality_max : ('l * 'r) t -> (disallowed * 'r) t
  val set_linearity_min : ('l * 'r) t -> ('l * disallowed) t
  val set_linearity_max : ('l * 'r) t -> (disallowed * 'r) t
  val set_uniqueness_min : ('l * 'r) t -> ('l * disallowed) t
  val set_uniqueness_max : ('l * 'r) t -> (disallowed * 'r) t
  val constrain_legacy : lr -> Const.t

  val close_over : lr -> l
  val partial_apply : (allowed * 'r) t -> l

  val newvar_below_comonadic : ?hint:string -> ('l * allowed) t -> ('l * 'r) t
    * bool
end

module type S = sig
  type nonrec allowed = allowed
  type nonrec disallowed = disallowed

  module Locality : sig
    module Const : sig
      type t = Global | Local
      include Const with type t := t
    end
    type error = unit

    include Common with module Const := Const and type error := error

    val global : lr
    val local : lr
    val constrain_legacy : (allowed * 'r) t -> Const.t
  end

  module Regionality : sig
    module Const : sig
      type t = Global | Regional | Local
      include Const with type t := t
    end
    type error = unit
    include Common with module Const := Const and type error := error

    val global : lr
    val regional : lr
    val local : lr
    val constrain_legacy : (allowed * 'r) t -> Const.t
  end

  module Linearity : sig
    module Const : sig
      type t = Many | Once
      include Const with type t := t
    end
    type error = unit
    include Common with module Const := Const and type error := error

    val many : lr
    val once : lr
    val constrain_legacy : (allowed * 'r) t -> Const.t
  end

  module Uniqueness : sig

    module Const : sig

      type t = Unique | Shared
      include Const with type t := t
    end
    type error = unit
    include Common with module Const := Const and type error := error

    val shared : lr
    val unique : lr
    val constrain_legacy : ('l * allowed) t -> Const.t
  end

  module Value :
  Alloc_or_Value
    with module Locality := Regionality
    and module Uniqueness := Uniqueness
    and module Linearity := Linearity


  module Alloc :
  Alloc_or_Value
    with module Locality := Locality
    and module Uniqueness := Uniqueness
    and module Linearity := Linearity

  val unique_to_linear : ('l * 'r) Uniqueness.t -> ('r * 'l) Linearity.t
  val linear_to_unique : ('l * 'r) Linearity.t -> ('r * 'l) Uniqueness.t
  val local_to_regional : ('l * 'r) Locality.t -> ('l * disallowed) Regionality.t
  val regional_to_local : ('l * 'r) Regionality.t -> ('l * 'r) Locality.t
  val locality_as_regionality : ('l * 'r) Locality.t -> ('l * 'r) Regionality.t
  val regional_to_global : ('l * 'r) Regionality.t -> ('l * 'r) Locality.t
  val global_to_regional : ('l * 'r) Locality.t -> (disallowed * 'r) Regionality.t
  val alloc_as_value : ('l * 'r) Alloc.t -> ('l * 'r) Value.t
  val alloc_to_value_l2r : ('l * 'r) Alloc.t -> ('l * disallowed) Value.t

  (* not used; only for completeness*)
  val alloc_to_value_g2r : ('l * 'r) Alloc.t -> (disallowed * 'r) Value.t
  val value_to_alloc_r2g : ('l * 'r) Value.t -> ('l * 'r) Alloc.t
  val value_to_alloc_r2l : ('l * 'r) Value.t -> ('l * 'r) Alloc.t

  module Const : sig
  val unique_to_linear : Uniqueness.Const.t -> Linearity.Const.t
  end

end