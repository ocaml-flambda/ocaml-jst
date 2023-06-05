type allowed = private Allowed
type disallowed = private Disallowed
type left_only = allowed * disallowed
type right_only = disallowed * allowed
type both = allowed * allowed
type ('a, 'b) eq = Refl : ('a, 'a) eq
type 'a positive = 'b * 'c constraint 'a = 'b * 'c
type 'a negative = 'c * 'b constraint 'a = 'b * 'c


module type Lattice = sig
  type t

  val min : t
  val max : t

  val le : t -> t -> bool
  val join : t -> t -> t
  val meet : t -> t -> t
  val print : Format.formatter -> t -> unit
end

(** A category where objects are lattices and morphisms are monotone functions.
    Among those monotone functions some will have left and right adjoints.*)
module type Mono_lattices = sig

  (** object in this category, where 'a is the type of elements in that lattice object *)
  type 'a obj

  (** given objects, return the lattice structure *)
  val obj : 'a obj -> (module Lattice with type t = 'a)

  val eq_obj : 'a obj -> 'b obj -> ('a, 'b) eq option

  (** 'd = 'l * 'r
     l = allowed means the morphism have right adjoint
     r = allowed means the morphism have left adjoint *)
  type ('a, 'b, 'd) morph

  val id : ('a, 'a, 'd) morph

  val compose :
    'b obj -> ('b, 'c, 'd) morph -> ('a, 'b, 'd) morph -> ('a, 'c, 'd) morph

  (* left_only means allowed * disallowed, which is weaker than what we want,
     which is \exists r. allowed * disallowed. But ocaml doesn't like existentials,
     and this weakened version is good enough for us *)
  val left_adjoint : ('a, 'b, 'l * allowed) morph -> ('b, 'a, left_only) morph
  val right_adjoint : ('a, 'b, allowed * 'r) morph -> ('b, 'a, right_only) morph

  (* forget whether a function can be on the right. *)
  val disallow_right :
    ('a, 'b, 'l * 'r) morph -> ('a, 'b, 'l * disallowed) morph

  val disallow_left : ('a, 'b, 'l * 'r) morph -> ('a, 'b, disallowed * 'r) morph
  val allow_right : ('a, 'b, 'l * allowed) morph -> ('a, 'b, 'l * 'r) morph
  val allow_left : ('a, 'b, allowed * 'r) morph -> ('a, 'b, 'l * 'r) morph
  val apply : 'a obj -> 'b obj -> ('a, 'b, 'd) morph -> 'a -> 'b

  val print_morph :
    'a obj -> 'b obj -> Format.formatter -> ('a, 'b, 'd) morph -> unit
end

module type S = sig
  type changes
  val undo_changes : changes -> unit
  val append_changes : (changes ref -> unit) ref
  module Mono_solver (C : Mono_lattices) : sig
    type ('a, 'd) mode
    type 'a var

    val min : 'a C.obj -> ('a, 'l * 'r) mode
    val max : 'a C.obj -> ('a, 'l * 'r) mode
    val of_const : 'a -> ('a, 'l * 'r) mode

    val apply :
      'a C.obj ->
      'b C.obj ->
      ('a, 'b, 'd0 * 'd1) C.morph ->
      ('a, 'd0 * 'd1) mode ->
      ('b, 'd0 * 'd1) mode

    val submode :
      'a C.obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (unit, unit) result

    (* val submode_try :
      'a C.obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (change Log.log, unit) result *)

    val equate :
      'a C.obj -> ('a, both) mode -> ('a, both) mode -> (unit, unit) result

    val submode_exn :
      'a C.obj -> ('a, allowed * 'r) mode -> ('a, 'l * allowed) mode -> unit

    val equate_exn : 'a C.obj -> ('a, both) mode -> ('a, both) mode -> unit
    val newvar : ?hint:string -> 'a C.obj -> ('a, 'l * 'r) mode
    val constrain_lower : 'a C.obj -> ('a, allowed * 'r) mode -> 'a
    val constrain_upper : 'a C.obj -> ('a, 'e * allowed) mode -> 'a

    val newvar_above :
      ?hint:string ->
      'a C.obj ->
      ('a, allowed * 'r_) mode ->
      ('a, 'l * 'r) mode * bool

    val newvar_below :
      ?hint:string ->
      'a C.obj ->
      ('a, 'l_ * allowed) mode ->
      ('a, 'l * 'r) mode * bool

    val join : 'a C.obj -> ('a, allowed * 'r) mode list -> ('a, left_only) mode
    val meet : 'a C.obj -> ('a, 'l * allowed) mode list -> ('a, right_only) mode
    val check_const : 'a C.obj -> ('a, 'd0 * 'd1) mode -> 'a option

    val print :
      'a C.obj ->
      ?verbose:bool ->
      ?axis:string ->
      Format.formatter ->
      ('a, 'l * 'r) mode ->
      unit
  end

  module Polarized_solver (C : Mono_lattices) : sig
    module S : module type of Mono_solver (C)

    type 'a neg = Neg of 'a [@@unboxed]
    type 'a pos = Pos of 'a [@@unboxed]

    (* This category contains two kinds of objects:
      Those from the base category, those from the base category but dualized *)
    type 'a obj =
      | Positive : 'a C.obj -> 'a pos obj
      | Negative : 'a C.obj -> 'a neg obj

    (* 'a and 'b are source and destination
      'd and 'e are source and desitnation adjoint status *)
    type ('a, 'd, 'b, 'e) morph =
      | Pos_Pos :
          ('a, 'b, 'd) C.morph
          -> ('a pos, 'd positive, 'b pos, 'd positive) morph
      | Pos_Neg :
          ('a, 'b, 'd) C.morph
          -> ('a pos, 'd positive, 'b neg, 'd negative) morph
      | Neg_Pos :
          ('a, 'b, 'd) C.morph
          -> ('a neg, 'd negative, 'b pos, 'd positive) morph
      | Neg_Neg :
          ('a, 'b, 'd) C.morph
          -> ('a neg, 'd negative, 'b neg, 'd negative) morph

    (* id and compose not used; just for fun *)
    val id : 'a obj -> ('a, 'l * 'r, 'a, 'l * 'r) morph

    val compose :
      'b obj ->
      ('b, 'bl * 'br, 'c, 'cl * 'cr) morph ->
      ('a, 'al * 'ar, 'b, 'bl * 'br) morph ->
      ('a, 'al * 'ar, 'c, 'cl * 'cr) morph

    type ('a, 'd) mode =
      | Positive : ('a, 'd) S.mode -> ('a pos, 'd positive) mode
      | Negative : ('a, 'd) S.mode -> ('a neg, 'd negative) mode

    val disallow_right : ('a, 'l * 'r) mode -> ('a, 'l * disallowed) mode
    val disallow_left : ('a, 'l * 'r) mode -> ('a, disallowed * 'r) mode
    val allow_right : ('a, 'l * allowed) mode -> ('a, 'l * 'r) mode
    val allow_left : ('a, allowed * 'r) mode -> ('a, 'l * 'r) mode

    val apply :
      'a obj ->
      'b obj ->
      ('a, 'd0 * 'd1, 'b, 'e0 * 'e1) morph ->
      ('a, 'd0 * 'd1) mode ->
      ('b, 'e0 * 'e1) mode

    val of_const : 'a obj -> 'a -> ('a, 'l * 'r) mode
    val min : 'a obj -> ('a, 'l * 'r) mode
    val max : 'a obj -> ('a, 'l * 'r) mode
    val constrain_lower : 'a obj -> ('a, allowed * 'r) mode -> 'a
    val constrain_upper : 'a obj -> ('a, 'l * allowed) mode -> 'a
    val newvar : ?hint:string -> 'a obj -> ('a, 'l * 'r) mode

    val submode :
      'a obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (unit, unit) result

    (* val submode_try :
      'a obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (change Log.log, unit) result *)

    val equate :
      'a obj -> ('a, both) mode -> ('a, both) mode -> (unit, unit) result

    val submode_exn :
      'a obj -> ('a, allowed * 'r) mode -> ('a, 'l * allowed) mode -> unit

    val equate_exn : 'a obj -> ('a, both) mode -> ('a, both) mode -> unit

    val newvar_above :
      ?hint:string ->
      'a obj ->
      ('a, allowed * 'r_) mode ->
      ('a, 'l * 'r) mode * bool

    val newvar_below :
      ?hint:string ->
      'a obj ->
      ('a, 'l_ * allowed) mode ->
      ('a, 'l * 'r) mode * bool

    val join : 'a obj -> ('a, allowed * 'r) mode list -> ('a, left_only) mode
    val meet : 'a obj -> ('a, 'l * allowed) mode list -> ('a, right_only) mode
    val check_const : 'a obj -> ('a, 'l * 'r) mode -> 'a option

    val print :
      'a obj ->
      ?verbose:bool ->
      ?axis:string ->
      Format.formatter ->
      ('a, 'l * 'r) mode ->
      unit
  end
end