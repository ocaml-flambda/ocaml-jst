(* Modes *)
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

module Locality = struct
    type const = Global | Local
    type t = const mode
end

module Uniqueness = struct
    type const = Unique | Shared
    type t = const mode
end

module Linearity = struct
    module D = Uniqueness

    type const = Many | Once

    type t = D.const dmode

end

module Alloc = struct
    type const = (Locality.const, Uniqueness.const, Linearity.const) modes
    type t = (Locality.t, Uniqueness.t, Linearity.t) modes
end

module Regionality = struct
    type const =
    | Global
    | Regional
    | Local

    type t = {
        r_as_l : Locality.t;
        r_as_g : Locality.t
      }
end

module Value = struct
    type const = (Regionality.const, Uniqueness.const, Linearity.const) modes
    type t =
    (Regionality.t,
     Uniqueness.t,
     Linearity.t) modes
end
