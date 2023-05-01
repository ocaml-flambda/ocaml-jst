(* Modes *)

(* this module exists to break the circular dependency between types and modes:
    backtrack in types.ml refers to mode variables; and solver in mode.ml invokes
    backtrack functions. *)
type 'a var = {
  mutable upper: 'a;
  mutable lower: 'a;
  mutable vlower: 'a var list;
  mutable mark: bool;
  mvid: int;
}

type 'a mode =
  | Amode of 'a
  | Amodevar of 'a var

type 'a dmode = Dualized of 'a mode

type ('loc, 'u, 'lin) modes =
{ locality : 'loc
; uniqueness : 'u
; linearity : 'lin
}

module Locality : sig
    type const = Global | Local
    type t = const mode
end

module Uniqueness : sig
    type const = Unique | Shared
    type t = const mode
end

module Linearity : sig
    type const = Many | Once
    type t = Uniqueness.const dmode
end

module Alloc : sig
    type const = (Locality.const, Uniqueness.const, Linearity.const) modes
    type t = (Locality.t, Uniqueness.t, Linearity.t) modes
end

module Regionality : sig
    type const =
    | Global
    | Regional
    | Local

    type t = {
        r_as_l : Locality.t;
        r_as_g : Locality.t
      }
end

module Value : sig
    type const = (Regionality.const, Uniqueness.const, Linearity.const) modes
    type t =
    (Regionality.t,
     Uniqueness.t,
     Linearity.t) modes
end
