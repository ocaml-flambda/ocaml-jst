include Mode_intf

open Solver
open Solver_intf

type nonrec allowed = allowed
type nonrec disallowed = disallowed

module Mono_lattices = struct
  module Product = struct
    type ('a0, 'a1) t = 'a0 * 'a1

    (* type aware indexing into a tuple *)
    type ('a0, 'a1, 'a) axis =
      | Axis0 : ('a0, 'a1, 'a0) axis
      | Axis1 : ('a0, 'a1, 'a1) axis

    let print_axis : type a0 a1 a. Format.formatter -> (a0, a1, a) axis -> unit
        =
     fun ppf -> function
      | Axis0 -> Format.fprintf ppf "0"
      | Axis1 -> Format.fprintf ppf "1"

    let proj (type a0 a1 a) : (a0, a1, a) axis -> a0 * a1 -> a = function
      | Axis0 -> fun (x, _) -> x
      | Axis1 -> fun (_, x) -> x

    let eq_axis (type a0 a1 a b) :
        (a0, a1, a) axis -> (a0, a1, b) axis -> (a, b) eq option =
     fun a b ->
      match (a, b) with
      | Axis0, Axis0 -> Some Refl
      | Axis1, Axis1 -> Some Refl
      | _ -> None

    type ('a0, 'a1, 'a, 'b0, 'b1, 'b) saxis =
      | SAxis0 : ('a0, 'a1, 'a0, 'b0, 'a1, 'b0) saxis
      | SAxis1 : ('a0, 'a1, 'a1, 'a0, 'b1, 'b1) saxis

    let flip (type a0 a1 a b0 b1 b) :
        (a0, a1, a, b0, b1, b) saxis -> (b0, b1, b, a0, a1, a) saxis = function
      | SAxis0 -> SAxis0
      | SAxis1 -> SAxis1

    let set (type a0 a1 a b0 b1 b) :
        (a0, a1, a, b0, b1, b) saxis -> (a -> b) -> (a0, a1) t -> (b0, b1) t =
      function
      | SAxis0 -> fun f (a0, a1) -> (f a0, a1)
      | SAxis1 -> fun f (a0, a1) -> (a0, f a1)

    let diag (type a0 a1 a) : (a0, a1, a) axis -> (a0, a1, a, a0, a1, a) saxis =
      function
      | Axis0 -> SAxis0
      | Axis1 -> SAxis1

    let src (type a0 a1 a b0 b1 b) :
        (a0, a1, a, b0, b1, b) saxis -> (a0, a1, a) axis = function
      | SAxis0 -> Axis0
      | SAxis1 -> Axis1

    let dst (type a0 a1 a b0 b1 b) :
        (a0, a1, a, b0, b1, b) saxis -> (b0, b1, b) axis = function
      | SAxis0 -> Axis0
      | SAxis1 -> Axis1

    let update (type a0 a1 a) : (a0, a1, a) axis -> a -> a0 * a1 -> a0 * a1 =
     fun ax a t -> set (diag ax) (fun _ -> a) t

    module Lattice (L0 : Lattice) (L1 : Lattice) = struct
      type nonrec t = (L0.t, L1.t) t

      let min = (L0.min, L1.min)
      let max = (L0.max, L1.max)
      let le (a0, a1) (b0, b1) = L0.le a0 b0 && L1.le a1 b1
      let join (a0, a1) (b0, b1) = (L0.join a0 b0, L1.join a1 b1)
      let meet (a0, a1) (b0, b1) = (L0.meet a0 b0, L1.meet a1 b1)

      let print ppf (a0, a1) =
        Format.fprintf ppf "%a,%a" L0.print a0 L1.print a1
    end
  end

  module Opposite (L : Lattice) : Lattice with type t = L.t = struct
    type t = L.t

    let min = L.max
    let max = L.min
    let le a b = L.le b a
    let join = L.meet
    let meet = L.join
    let print = L.print
  end

  module Locality = struct
    type t = Global | Local

    let min = Global
    let max = Local

    let le a b =
      match (a, b) with Global, _ | _, Local -> true | Local, Global -> false

    let join a b =
      match (a, b) with
      | Local, _ | _, Local -> Local
      | Global, Global -> Global

    let meet a b =
      match (a, b) with
      | Global, _ | _, Global -> Global
      | Local, Local -> Local

    let print ppf = function
      | Global -> Format.fprintf ppf "Global"
      | Local -> Format.fprintf ppf "Local"
  end

  module Regionality = struct
    type t = Global | Regional | Local

    let min = Global
    let max = Local

    let le a b =
      match (a, b) with
      | Global, _ -> true
      | Regional, Global -> false
      | Regional, _ -> true
      | Local, Local -> true
      | Local, _ -> false

    let join a b =
      match (a, b) with
      | Local, _ | _, Local -> Local
      | Regional, _ | _, Regional -> Regional
      | Global, Global -> Global

    let meet a b =
      match (a, b) with
      | Global, _ | _, Global -> Global
      | Regional, _ | _, Regional -> Regional
      | Local, Local -> Local

    let print ppf = function
      | Global -> Format.fprintf ppf "Global"
      | Regional -> Format.fprintf ppf "Regional"
      | Local -> Format.fprintf ppf "Local"
  end

  module Uniqueness = struct
    type t = Unique | Shared

    let min = Unique
    let max = Shared

    let le a b =
      match (a, b) with
      | Unique, _ | _, Shared -> true
      | Shared, Unique -> false

    let join a b =
      match (a, b) with
      | Shared, _ | _, Shared -> Shared
      | Unique, Unique -> Unique

    let meet a b =
      match (a, b) with
      | Unique, _ | _, Unique -> Unique
      | Shared, Shared -> Shared

    let print ppf = function
      | Shared -> Format.fprintf ppf "Shared"
      | Unique -> Format.fprintf ppf "Unique"
  end

  module Uniqueness_op = Opposite (Uniqueness)

  module Linearity = struct
    type t = Many | Once

    let min = Many
    let max = Once

    let le a b =
      match (a, b) with Many, _ | _, Once -> true | Once, Many -> false

    let join a b =
      match (a, b) with Once, _ | _, Once -> Once | Many, Many -> Many

    let meet a b =
      match (a, b) with Many, _ | _, Many -> Many | Once, Once -> Once

    let print ppf = function
      | Once -> Format.fprintf ppf "Once"
      | Many -> Format.fprintf ppf "Many"
  end

  module Locality_Linearity = Product.Lattice (Locality) (Linearity)
  module Regionality_Linearity = Product.Lattice (Regionality) (Linearity)

  type 'a obj =
    | Locality : Locality.t obj
    | Regionality : Regionality.t obj
    (* use the flipped version of uniqueness, so that unique_to_linear is monotone *)
    | Uniqueness_op : Uniqueness_op.t obj
    | Linearity : Linearity.t obj
    | Locality_Linearity : Locality_Linearity.t obj
    | Regionality_Linearity : Regionality_Linearity.t obj

  let proj_obj :
      type a0 a1 a. (a0, a1, a) Product.axis -> (a0, a1) Product.t obj -> a obj
      = function
    | Axis0 -> (
        function
        | Locality_Linearity -> Locality | Regionality_Linearity -> Regionality)
    | Axis1 -> (
        function
        | Locality_Linearity -> Linearity | Regionality_Linearity -> Linearity)

  let obj : type a. a obj -> (module Lattice with type t = a) = function
    | Locality -> (module Locality)
    | Regionality -> (module Regionality)
    | Uniqueness_op -> (module Uniqueness_op)
    | Linearity -> (module Linearity)
    | Locality_Linearity -> (module Locality_Linearity)
    | Regionality_Linearity -> (module Regionality_Linearity)

  let eq_obj : type a b. a obj -> b obj -> (a, b) eq option =
   fun a b ->
    match (a, b) with
    | Locality, Locality -> Some Refl
    | Regionality, Regionality -> Some Refl
    | Uniqueness_op, Uniqueness_op -> Some Refl
    | Linearity, Linearity -> Some Refl
    | Locality_Linearity, Locality_Linearity -> Some Refl
    | Regionality_Linearity, Regionality_Linearity -> Some Refl
    | _ -> None

  type ('a, 'b, 'd) morph =
    | Id : ('a, 'a, 'd) morph
    (* the following two are special because they have adjoint
       which is needed to make compose type check (note that compose requires
       all morphs have the same 'l and 'r ) *)
    | Const_min : ('a, 'b, 'd * disallowed) morph
    | Const_max : ('a, 'b, disallowed * 'd) morph
    (* projection from product to axis *)
    | Proj :
        ('a0, 'a1, 'a) Product.axis
        -> (('a0, 'a1) Product.t, 'a, 'l * 'r) morph
    (* pushes to top except specified axis *)
    | Max_with :
        ('a0, 'a1, 'a) Product.axis
        -> ('a, ('a0, 'a1) Product.t, disallowed * 'r) morph
    (* pushes to bot except specified axis *)
    | Min_with :
        ('a0, 'a1, 'a) Product.axis
        -> ('a, ('a0, 'a1) Product.t, 'l * disallowed) morph
    | Set :
        ('a0, 'a1, 'a, 'b0, 'b1, 'b) Product.saxis * ('a, 'b, 'd) morph
        -> (('a0, 'a1) Product.t, ('b0, 'b1) Product.t, 'd) morph
    | Unique_to_linear : (Uniqueness.t, Linearity.t, 'l * 'r) morph
    | Linear_to_unique : (Linearity.t, Uniqueness.t, 'l * 'r) morph
    (* following is a chain of adjunction (complete and cannot extend in
       either direction) *)
    | Local_to_regional : (Locality.t, Regionality.t, 'l * disallowed) morph
    | Regional_to_local : (Regionality.t, Locality.t, 'l * 'r) morph
    | Locality_as_regionality : (Locality.t, Regionality.t, 'l * 'r) morph
    | Regional_to_global : (Regionality.t, Locality.t, 'l * 'r) morph
    | Global_to_regional : (Locality.t, Regionality.t, disallowed * 'r) morph
    (* composing morphisms  *)
    | Compose :
        'b obj * ('b, 'c, 'd) morph * ('a, 'b, 'd) morph
        -> ('a, 'c, 'd) morph

  (* let rec print_obj : type a. Format.formatter -> a obj -> unit =
      fun ppf -> function
       | Locality -> Format.fprintf ppf "locality"
       | Regionality -> Format.fprintf ppf "regionality"
       | Uniqueness_op -> Format.fprintf ppf "uniqueness_op"
       | Linearity -> Format.fprintf ppf "linearity"
       | Product objs -> Format.fprintf ppf "product(%a)" print_objs objs

     and print_objs :
         type a0 a1. Format.formatter -> (a0 obj, a1 obj) Product.t -> unit =
      fun ppf (obj0, obj1) ->
       Format.fprintf ppf "%a,%a" print_obj obj0 print_obj obj1 *)

  let rec print_morph :
      type a b d. a obj -> b obj -> Format.formatter -> (a, b, d) morph -> unit
      =
   fun src dst ppf -> function
    | Id -> Format.fprintf ppf "id"
    | Const_min -> Format.fprintf ppf "const_min"
    | Const_max -> Format.fprintf ppf "const_max"
    | Proj ax -> Format.fprintf ppf "proj_%a" Product.print_axis ax
    | Max_with ax -> Format.fprintf ppf "max_with_%a" Product.print_axis ax
    | Min_with ax -> Format.fprintf ppf "min_with_%a" Product.print_axis ax
    | Set _ -> Format.fprintf ppf "set"
    | Unique_to_linear -> Format.fprintf ppf "unique_to_linear"
    | Linear_to_unique -> Format.fprintf ppf "linear_to_unique"
    | Local_to_regional -> Format.fprintf ppf "local_to_regional"
    | Regional_to_local -> Format.fprintf ppf "regional_to_local"
    | Locality_as_regionality -> Format.fprintf ppf "locality_as_regionality"
    | Regional_to_global -> Format.fprintf ppf "regional_to_global"
    | Global_to_regional -> Format.fprintf ppf "global_to_regional"
    | Compose (mid, f0, f1) ->
        Format.fprintf ppf "%a | %a" (print_morph mid dst) f0
          (print_morph src mid) f1

  (* let rec src : type a b d. (a, b, d) morph -> a obj = function
     | Id a -> a
     | Const_min (a, _) -> a
     | Const_max (a, _) -> a
     | Proj (objs, _) -> Product objs
     | Max_with (objs, ax) -> Product.proj (lift ax) objs
     | Min_with (objs, ax) -> Product.proj (lift ax) objs
     | Map (f0, f1) -> Product (src f0, src f1)
     | Unique_to_linear -> Uniqueness_op
     | Linear_to_unique -> Linearity
     | Local_to_regional -> Locality
     | Regional_to_local -> Regionality
     | Locality_as_regionality -> Locality
     | Regional_to_global -> Regionality
     | Global_to_regional -> Locality
     | Compose (_, f1) -> src f1 *)

  let id = Id

  let linear_to_unique = function
    | Linearity.Many -> Uniqueness.Shared
    | Linearity.Once -> Uniqueness.Unique

  let unique_to_linear = function
    | Uniqueness.Unique -> Linearity.Once
    | Uniqueness.Shared -> Linearity.Many

  let locality_as_regionality = function
    | Locality.Global -> Regionality.Global
    | Locality.Local -> Regionality.Local

  let regional_to_local = function
    | Regionality.Regional -> Locality.Local
    | Regionality.Local -> Locality.Local
    | Regionality.Global -> Locality.Global

  let regional_to_global = function
    | Regionality.Regional -> Locality.Global
    | Regionality.Local -> Locality.Local
    | Regionality.Global -> Locality.Global

  let local_to_regional = function
    | Locality.Local -> Regionality.Regional
    | Locality.Global -> Regionality.Global

  let global_to_regional = function
    | Locality.Local -> Regionality.Local
    | Locality.Global -> Regionality.Regional

  (* let rec length : type a b d. (a, b, d) morph -> int = function
     | Compose (f, g) -> length f + length g
     | _ -> 1 *)

  let rec apply : type a b d. a obj -> b obj -> (a, b, d) morph -> a -> b =
   fun src dst f a ->
    match f with
    | Id -> a
    | Proj ax -> Product.proj ax a
    | Max_with ax -> (
        match dst with
        | Locality_Linearity -> Product.update ax a Locality_Linearity.max
        | Regionality_Linearity -> Product.update ax a Regionality_Linearity.max
        )
    | Min_with ax -> (
        match dst with
        | Locality_Linearity -> Product.update ax a Locality_Linearity.min
        | Regionality_Linearity -> Product.update ax a Regionality_Linearity.min
        )
    | Const_min -> let module L = (val obj dst) in L.min
    | Const_max -> let module L = (val obj dst) in L.max
    | Compose (mid, f, g) -> apply mid dst f (apply src mid g a)
    | Unique_to_linear -> unique_to_linear a
    | Linear_to_unique -> linear_to_unique a
    | Locality_as_regionality -> locality_as_regionality a
    | Regional_to_local -> regional_to_local a
    | Regional_to_global -> regional_to_global a
    | Local_to_regional -> local_to_regional a
    | Global_to_regional -> global_to_regional a
    | Set (ax, f) ->
        Product.set ax
          (apply
             (proj_obj (Product.src ax) src)
             (proj_obj (Product.dst ax) dst)
             f)
          a

  (* m0 wraps around m1;
     raise NotCollapse if m0 and m1 cannot collapse
     TODO: finer grained: tells if collapsed on each side.
  *)
  let rec maybe_compose :
      type a b c d.
      b obj -> (b, c, d) morph -> (a, b, d) morph -> (a, c, d) morph option =
   fun mid m0 m1 ->
    match (m0, m1) with
    | Id, m -> Some m
    | m, Id -> Some m
    | Const_min, _ -> Some Const_min
    | Const_max, _ -> Some Const_max
    | Proj ax0, Max_with ax1 -> (
        match Product.eq_axis ax0 ax1 with
        | None -> Some Const_max
        | Some Refl -> Some Id)
    | Proj ax0, Min_with ax1 -> (
        match Product.eq_axis ax0 ax1 with
        | None -> Some Const_min
        | Some Refl -> Some Id)
    | Min_with ax0, Proj ax1 -> (
        match (ax0, ax1) with
        | Product.Axis0, Product.Axis0 -> Some (Set (Product.SAxis1, Const_min))
        | Product.Axis1, Product.Axis1 -> Some (Set (Product.SAxis0, Const_min))
        | _ -> None)
    | Max_with ax0, Proj ax1 -> (
        match (ax0, ax1) with
        | Product.Axis0, Product.Axis0 -> Some (Set (Product.SAxis1, Const_max))
        | Product.Axis1, Product.Axis1 -> Some (Set (Product.SAxis0, Const_max))
        | _ -> None)
    | Proj _, Const_min -> Some Const_min
    | Proj _, Const_max -> Some Const_max
    | Max_with _, Const_max -> Some Const_max
    | Min_with _, Const_min -> Some Const_min
    | Unique_to_linear, Const_min -> Some Const_min
    | Linear_to_unique, Const_min -> Some Const_min
    | Unique_to_linear, Const_max -> Some Const_max
    | Linear_to_unique, Const_max -> Some Const_max
    | Unique_to_linear, Linear_to_unique -> Some Id
    | Linear_to_unique, Unique_to_linear -> Some Id
    | Regional_to_local, Locality_as_regionality -> Some Id
    | Regional_to_global, Locality_as_regionality -> Some Id
    | Set (ax0, f0), Set (ax1, f1) -> (
        match (ax0, ax1) with
        | Product.SAxis0, Product.SAxis0 ->
            Some
              (Set (Product.SAxis0, compose (proj_obj Product.Axis0 mid) f0 f1))
        | Product.SAxis1, Product.SAxis1 ->
            Some
              (Set (Product.SAxis1, compose (proj_obj Product.Axis1 mid) f0 f1))
        | _ -> None)
    (* the following are important: look inside compose *)
    | Compose (mid', f0, f1), g -> (
        match maybe_compose mid f1 g with
        | Some m -> Some (compose mid' f0 m)
        (* the check needed to prevent infinite loop *)
        | None -> None)
    | f, Compose (mid', g0, g1) -> (
        match maybe_compose mid f g0 with
        | Some m -> Some (compose mid' m g1)
        | None -> None)
    | Regional_to_local, Local_to_regional -> Some Id
    | Regional_to_local, Global_to_regional -> Some Const_max
    | Regional_to_local, Const_min -> Some Const_min
    | Regional_to_local, Const_max -> Some Const_max
    | Regional_to_global, Local_to_regional -> Some Const_min
    | Regional_to_global, Global_to_regional -> Some Id
    | Regional_to_global, Const_min -> Some Const_min
    | Regional_to_global, Const_max -> Some Const_max
    | Local_to_regional, Regional_to_local -> None
    | Local_to_regional, Regional_to_global -> None
    | Local_to_regional, Const_min -> Some Const_min
    | Local_to_regional, Const_max -> None
    | Locality_as_regionality, Regional_to_local -> None
    | Locality_as_regionality, Regional_to_global -> None
    | Locality_as_regionality, Const_min -> Some Const_min
    | Locality_as_regionality, Const_max -> Some Const_max
    | Global_to_regional, Regional_to_local -> None
    | Global_to_regional, Regional_to_global -> None
    | Global_to_regional, Const_min -> None
    | Global_to_regional, Const_max -> Some Const_max
    | Proj _, Proj _ -> None
    | Proj _, Set _ ->
        (* TODO: collapse this *)
        None
    | Min_with _, _ -> None
    | Max_with _, _ -> None
    | _, Proj _ -> None
    | Set _, _ -> None

  and compose :
      type a b c d.
      b obj -> (b, c, d) morph -> (a, b, d) morph -> (a, c, d) morph =
   fun mid f g ->
    match maybe_compose mid f g with Some m -> m | None -> Compose (mid, f, g)

  let rec left_adjoint :
      type a b l.
      (a, b, l * allowed) morph -> (b, a, allowed * disallowed) morph = function
    | Id -> Id
    | Proj Product.Axis0 -> Min_with Product.Axis0
    | Proj Product.Axis1 -> Min_with Product.Axis1
    | Max_with Product.Axis0 -> Proj Product.Axis0
    | Max_with Product.Axis1 -> Proj Product.Axis1
    | Compose (mid, f, g) -> Compose (mid, left_adjoint g, left_adjoint f)
    | Const_max -> Const_min
    | Unique_to_linear -> Linear_to_unique
    | Linear_to_unique -> Unique_to_linear
    | Global_to_regional -> Regional_to_global
    | Regional_to_global -> Locality_as_regionality
    | Locality_as_regionality -> Regional_to_local
    | Regional_to_local -> Local_to_regional
    | Set (ax, f) -> Set (Product.flip ax, left_adjoint f)

  let rec right_adjoint :
      type a b r.
      (a, b, allowed * r) morph -> (b, a, disallowed * allowed) morph = function
    | Id -> Id
    | Proj Product.Axis0 -> Max_with Product.Axis0
    | Proj Product.Axis1 -> Max_with Product.Axis1
    | Min_with Product.Axis0 -> Proj Product.Axis0
    | Min_with Product.Axis1 -> Proj Product.Axis1
    | Compose (mid, f, g) -> Compose (mid, right_adjoint g, right_adjoint f)
    | Const_min -> Const_max
    | Unique_to_linear -> Linear_to_unique
    | Linear_to_unique -> Unique_to_linear
    | Local_to_regional -> Regional_to_local
    | Regional_to_local -> Locality_as_regionality
    | Locality_as_regionality -> Regional_to_global
    | Regional_to_global -> Global_to_regional
    | Set (ax, f) -> Set (Product.flip ax, right_adjoint f)

  let disallow_right :
      type a b l r. (a, b, l * r) morph -> (a, b, l * disallowed) morph =
    Obj.magic

  let disallow_left :
      type a b l r. (a, b, l * r) morph -> (a, b, disallowed * r) morph =
    Obj.magic

  let allow_left :
      type a b l r. (a, b, allowed * r) morph -> (a, b, l * r) morph =
    Obj.magic

  let allow_right :
      type a b l r. (a, b, l * allowed) morph -> (a, b, l * r) morph =
    Obj.magic
end

module C = Mono_lattices
module S = Polarized_solver (C)

module type Obj = sig
  module Const : Const

  type const_s

  (* val obj_c : Const.t C.obj *)
  val obj_s : const_s S.obj
  val unpack : const_s -> Const.t
  val pack : Const.t -> const_s
end


module Common (Obj : Obj) = struct
  open Obj
  (* module Const = Const *)

  type 'd t = (const_s, 'd) S.mode
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t
  type error = unit

  let disallow_right m = S.disallow_right m
  let disallow_left m = S.disallow_left m
  let allow_left m = S.allow_left m
  let allow_right m = S.allow_right m
  let newvar ?hint () = S.newvar ?hint obj_s
  let min = S.min obj_s
  let max = S.max obj_s
  let newvar_above ?hint m = S.newvar_above ?hint obj_s m
  let newvar_below ?hint m = S.newvar_below ?hint obj_s m
  let submode m0 m1 : (unit, error) result = S.submode obj_s m0 m1
  let join l = S.join obj_s l
  let meet l = S.meet obj_s l
  let submode_exn m0 m1 = S.submode_exn obj_s m0 m1
  let equate m0 m1 = S.equate obj_s m0 m1
  let equate_exn m0 m1 = S.equate_exn obj_s m0 m1
  let print ?verbose ?axis ppf m = S.print obj_s ?verbose ?axis ppf m
  let print_simple ppf m = print ~verbose:false ?axis:None ppf m
  let constrain_upper m = Obj.unpack (S.constrain_upper obj_s m)
  let constrain_lower m = Obj.unpack (S.constrain_lower obj_s m)

  let of_const : type l r. Const.t -> (l * r) t =
   fun a -> S.of_const obj_s (Obj.pack a)

  let check_const m = Option.map Obj.unpack (S.check_const obj_s m)

end

module Locality = struct

  module Const = struct
    include C.Locality
    let legacy = Global
  end

  module Obj = struct
    module Const = Const
    type const_s = Const.t S.pos

    let obj_c = C.Locality
    let obj_s : const_s S.obj = S.Positive obj_c
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common (Obj)

  let global = of_const Global
  let local = of_const Local
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_lower
end

module Regionality = struct
  module Const = struct
    include C.Regionality
    let legacy = Global
  end
  module Obj = struct
    module Const = Const
    type const_s = Const.t S.pos

    let obj_c = C.Regionality
    let obj_s : const_s S.obj = S.Positive obj_c
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common (Obj)

  let global = of_const Global
  let regional = of_const Regional
  let local = of_const Local
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_lower
end

module Linearity = struct
  module Const = struct
    include C.Linearity
    let legacy = Many
  end

  module Obj = struct
    module Const = Const
    type const_s = Const.t S.pos

    let obj_c = C.Linearity
    let obj_s : const_s S.obj = S.Positive obj_c
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common (Obj)

  let many = of_const Many
  let once = of_const Once
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_lower
end

module Uniqueness = struct

  module Const = struct
    include C.Uniqueness
    let legacy = Shared
  end
  module Obj = struct
    module Const = Const
    (* the negation of Uniqueness_op gives us the proper uniqueness *)
    type const_s = Const.t S.neg

    let obj_c = C.Uniqueness_op
    let obj_s : const_s S.obj = S.Negative obj_c
    let unpack (S.Neg a) = a
    let pack a = S.Neg a
  end

  include Common (Obj)

  let shared = of_const Shared
  let unique = of_const Unique
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_upper
end

let unique_to_linear m =
  S.apply Uniqueness.Obj.obj_s Linearity.Obj.obj_s
    (S.Neg_Pos C.Unique_to_linear) m

let linear_to_unique m =
  S.apply Linearity.Obj.obj_s Uniqueness.Obj.obj_s
    (S.Pos_Neg C.Linear_to_unique) m

let local_to_regional m =
  S.apply Locality.Obj.obj_s Regionality.Obj.obj_s
    (S.Pos_Pos C.Local_to_regional) (S.disallow_right m)

let regional_to_local m =
  S.apply Regionality.Obj.obj_s Locality.Obj.obj_s
    (S.Pos_Pos C.Regional_to_local) m

let locality_as_regionality m =
  S.apply Locality.Obj.obj_s Regionality.Obj.obj_s
    (S.Pos_Pos C.Locality_as_regionality) m

let regional_to_global m =
  S.apply Regionality.Obj.obj_s Locality.Obj.obj_s
    (S.Pos_Pos C.Regional_to_global) m

let global_to_regional m =
  S.apply Locality.Obj.obj_s Regionality.Obj.obj_s
    (S.Pos_Pos C.Global_to_regional) (S.disallow_left m)

module Const = struct
  let unique_to_linear a = C.unique_to_linear a
end


(* We now define alloc and value, each is a product of mode of opposite
   polarities (and thus cannot be defined in Mono_lattices).
   It is a simple wraper so that submoding on the product
   immediately translates to submoding on individual lattices. Note that if you
   want to combine lattices of the same polarity, you should make a native
   product lattice with native projections and adjunctions, like what we did in
   mode.ml, which is more efficient because one submoding doesn't translates to
   two submoding underneath.

   Alloc and Value differ only in the first axis so we do a bit of abstraction.
*)
module type Loc_or_Reg = sig
  include Common

  type const_prod = Const.t * Linearity.Const.t

  (* either Locality or Regionality *)
  val obj : Const.t C.obj

  (* either Locality_Linearity or Regionality_Linearity *)
  val obj_prod : const_prod C.obj
end

(* packed version where axes are packed into two groups, positvie and negative *)
module Alloc_or_Value (LR : Loc_or_Reg) = struct
  (* type 'd locality_t = (LR.Const.t S.pos, 'd) S.mode *)

  let lr_obj : _ S.obj = S.Positive LR.obj
  let unpack (S.Pos x) = x

  type a0 = LR.const_prod S.pos

  let obj0 : a0 S.obj = S.Positive LR.obj_prod

  type a1 = Uniqueness.Const.t S.neg

  let obj1 : a1 S.obj = S.Negative C.Uniqueness_op

  type 'd t = (a0, 'd) S.mode * (a1, 'd) S.mode
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t

  let min = (S.min obj0, S.min obj1)
  let max = (S.max obj0, S.max obj1)
  let disallow_right = Obj.magic
  let disallow_left = Obj.magic
  let allow_right = Obj.magic
  let allow_left = Obj.magic
  let newvar ?hint () = (S.newvar ?hint obj0, S.newvar ?hint obj1)

  let newvar_above ?hint (m0, m1) =
    let m0, b0 = S.newvar_above ?hint obj0 m0 in
    let m1, b1 = S.newvar_above ?hint obj1 m1 in
    ((m0, m1), b0 || b1)

  let newvar_below ?hint (m0, m1) =
    let m0, b0 = S.newvar_below ?hint obj0 m0 in
    let m1, b1 = S.newvar_below ?hint obj1 m1 in
    ((m0, m1), b0 || b1)

  let locality_of (m, _) =
    S.apply obj0 lr_obj (S.Pos_Pos (C.Proj C.Product.Axis0)) m

  let linearity_of (m, _) =
    S.apply obj0 Linearity.Obj.obj_s (S.Pos_Pos (C.Proj C.Product.Axis1)) m

  let uniqueness_of (_, m) = m

  type error = [ `Locality | `Uniqueness | `Linearity ]

  (* NB: state mutated when error *)
  let submode ((m00, m01) as m0) ((m10, m11) as m1) =
    match S.submode obj0 m00 m10 with
    | Error () -> (
        (* find out the offending axis *)
        match S.submode lr_obj (locality_of m0) (locality_of m1) with
        | Error () -> Error `Locality
        | Ok () -> (
            match Linearity.submode (linearity_of m0) (linearity_of m1) with
            | Ok () -> assert false (* sanity *)
            | Error () -> Error `Linearity))
    | Ok () -> (
        match S.submode obj1 m01 m11 with
        | Ok () -> Ok ()
        | Error () -> Error `Uniqueness)

  let equate m0 m1 =
    match submode m0 m1 with Error e -> Error e | Ok () -> submode m1 m0

  let submode_exn m0 m1 =
    match submode m0 m1 with
    | Ok () -> ()
    | Error _ -> invalid_arg "submode_exn"

  let equate_exn m0 m1 =
    match equate m0 m1 with Ok () -> () | Error _ -> invalid_arg "equate_exn"

  let print ?(verbose = true) ppf (m0, m1) =
    Format.fprintf ppf "%a,%a"
      (S.print obj0 ~verbose ~axis:"loc_lin")
      m0
      (S.print ~verbose ~axis:"uni" obj1)
      m1

  let print_simple ppf m = print ~verbose:false ppf m

  let constrain_lower (m0, m1) =
    match (S.constrain_lower obj0 m0, S.constrain_lower obj1 m1) with
    | S.Pos (locality, linearity), S.Neg uniqueness ->
        { locality; linearity; uniqueness }

  let constrain_upper (m0, m1) =
    match (S.constrain_upper obj0 m0, S.constrain_upper obj1 m1) with
    | S.Pos (locality, linearity), S.Neg uniqueness ->
        { locality; linearity; uniqueness }

  let constrain_legacy (m0, m1) =
    match (S.constrain_lower obj0 m0, S.constrain_upper obj1 m1) with
    | S.Pos (locality, linearity), S.Neg uniqueness ->
        { locality; linearity; uniqueness }

  let check_const m =
    let locality = Option.map unpack (S.check_const lr_obj (locality_of m)) in
    let linearity = Linearity.check_const (linearity_of m) in
    let uniqueness = Uniqueness.check_const (uniqueness_of m) in
    { locality; linearity; uniqueness }

  let of_const { locality; linearity; uniqueness } =
    ( S.of_const obj0 (S.Pos (locality, linearity)),
      S.of_const obj1 (S.Neg uniqueness) )

  (* global many, shared *)
  let legacy = (S.min obj0, S.max obj1)

  (* Below we package up the complex projection from alloc to three axes as if
     they live under alloc directly and uniformly. We define functions that operate
     on modes numerically, instead of defining symbolic functions *)
  (* type const = (LR.Const.t, Linearity.Const.t, Uniqueness.Const.t) modes *)

  let max_with_uniqueness uniqueness =
    (S.max obj0, Uniqueness.disallow_left uniqueness)

  let min_with_uniqueness uniqueness =
    (S.min obj0, Uniqueness.disallow_right uniqueness)

  let min_with_locality locality =
    let m0 =
      S.apply lr_obj obj0 (S.Pos_Pos (C.Min_with C.Product.Axis0))
        (S.disallow_right locality)
    in
    let m1 = S.min (S.Negative C.Uniqueness_op) in
    (m0, m1)

  let max_with_locality locality =
    let m0 =
      S.apply lr_obj obj0 (S.Pos_Pos (C.Max_with C.Product.Axis0))
        (S.disallow_left locality)
    in
    let m1 = S.max (S.Negative C.Uniqueness_op) in
    (m0, m1)

  let min_with_linearity linearity =
    let m0 =
      S.apply Linearity.Obj.obj_s obj0 (S.Pos_Pos (C.Min_with C.Product.Axis1))
        (S.disallow_right linearity)
    in
    let m1 = S.min (S.Negative C.Uniqueness_op) in
    (m0, m1)

  let max_with_linearity linearity =
    let m0 =
      S.apply Linearity.Obj.obj_s obj0 (S.Pos_Pos (C.Max_with C.Product.Axis1))
        (S.disallow_left linearity)
    in
    let m1 = S.max (S.Negative C.Uniqueness_op) in
    (m0, m1)

  let set_locality_max (m0, m1) =
    let m0 =
      S.apply obj0 obj0
        (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Const_max)))
        (S.disallow_left m0)
    in
    (m0, S.disallow_left m1)

  let set_locality_min (m0, m1) =
    let m0 =
      S.apply obj0 obj0
        (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Const_min)))
        (S.disallow_right m0)
    in
    (m0, S.disallow_right m1)

  let set_uniqueness_max (m0, _) =
    (S.disallow_left m0, S.disallow_left (S.allow_right Uniqueness.max))

  let set_uniqueness_min (m0, _) =
    (S.disallow_right m0, S.disallow_right (S.allow_left Uniqueness.min))

  let set_linearity_max (m0, m1) =
    let m0 =
      S.apply obj0 obj0
        (S.Pos_Pos (C.Set (C.Product.SAxis1, C.Const_max)))
        (S.disallow_left m0)
    in
    (m0, S.disallow_left m1)

  let set_linearity_min (m0, m1) =
    let m0 =
      S.apply obj0 obj0
        (S.Pos_Pos (C.Set (C.Product.SAxis1, C.Const_min)))
        (S.disallow_right m0)
    in
    (m0, S.disallow_right m1)

  let join l =
    let l0, l1 = List.split l in
    let m0 = S.join obj0 l0 in
    let m1 = S.join obj1 l1 in
    (m0, m1)

  let meet l =
    let l0, l1 = List.split l in
    let m0 = S.meet obj0 l0 in
    let m1 = S.meet obj1 l1 in
    (m0, m1)

  module Const = struct
    type t = (LR.Const.t, Linearity.Const.t, Uniqueness.Const.t) modes
    let min = {
      locality = LR.Const.min;
      linearity = Linearity.Const.min;
      uniqueness = Uniqueness.Const.min;
    }
    let max = {
      locality = LR.Const.max;
      linearity = Linearity.Const.max;
      uniqueness = Uniqueness.Const.max;
    }
    let le m0 m1 =
      LR.Const.le m0.locality m1.locality &&
      Uniqueness.Const.le m0.uniqueness m1.uniqueness &&
      Linearity.Const.le m0.linearity m1.linearity

    let print ppf m = print_simple ppf (of_const m)

    let legacy = {
      locality = LR.Const.legacy;
      linearity = Linearity.Const.legacy;
      uniqueness = Uniqueness.Const.legacy
    }

    let meet { locality = l0; linearity = l1; uniqueness = l2 }
        { locality = r0; linearity = r1; uniqueness = r2 } =
      {
        locality = LR.Const.meet l0 r0;
        linearity = Linearity.Const.meet l1 r1;
        uniqueness = Uniqueness.Const.meet l2 r2;
      }

    let join { locality = l0; linearity = l1; uniqueness = l2 }
        { locality = r0; linearity = r1; uniqueness = r2 } =
      {
        locality = LR.Const.join l0 r0;
        linearity = Linearity.Const.join l1 r1;
        uniqueness = Uniqueness.Const.join l2 r2;
      }

    (** constrain uncurried function ret_mode from arg_mode *)
    let close_over arg_mode =
      let locality = arg_mode.locality in
      (* uniqueness of the returned function is not constrained *)
      let uniqueness = Uniqueness.Const.min in
      let linearity =
        Linearity.Const.join arg_mode.linearity
          (* In addition, unique argument make the returning function once.
             In other words, if argument <= unique, returning function >= once.
             That is, returning function >= (dual of argument) *)
          (Const.unique_to_linear arg_mode.uniqueness)
      in
      { locality; uniqueness; linearity }

    (** constrain uncurried function ret_mode from the mode of the whole function *)
    let partial_apply alloc_mode =
      let locality = alloc_mode.locality in
      let uniqueness = Uniqueness.Const.min in
      let linearity = alloc_mode.linearity in
      { locality; uniqueness; linearity }
  end

  (** constrain uncurried function ret_mode from arg_mode *)
  let close_over arg_mode =
    let locality = min_with_locality (locality_of arg_mode) in
    (* uniqueness of the returned function is not constrained *)
    let linearity0 = min_with_linearity (linearity_of arg_mode) in
    let linearity1 = min_with_linearity (unique_to_linear (uniqueness_of arg_mode)) in
    (* In addition, unique argument make the returning function once.
        In other words, if argument <= unique, returning function >= once.
        That is, returning function >= (dual of argument) *)
    join [locality; linearity0; linearity1]

  (** constrain uncurried function ret_mode from the mode of the whole function *)
  let partial_apply alloc_mode = set_uniqueness_min alloc_mode

  let newvar_below_comonadic ?hint (m0, m1) =
    let m0, b0 = S.newvar_below ?hint obj0 m0 in
    ((m0, S.allow_right m1), b0)
end

(* module Alloc = Alloc_or_Value(Locality) *)
module Value = Alloc_or_Value (struct
  include Regionality

  type const_prod = Const.t * Linearity.Const.t

  let obj = Mono_lattices.Regionality
  let obj_prod = Mono_lattices.Regionality_Linearity
end)

module Alloc = Alloc_or_Value (struct
  include Locality

  type const_prod = Locality.Const.t * Linearity.Const.t

  let obj = Mono_lattices.Locality
  let obj_prod = Mono_lattices.Locality_Linearity
end)



let alloc_as_value (m0, m1) =
  let m0 =
    S.apply Alloc.obj0 Value.obj0
      (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Locality_as_regionality)))
      m0
  in
  (m0, m1)

let alloc_to_value_l2r (m0, m1) =
  let m0 =
    S.apply Alloc.obj0 Value.obj0
      (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Local_to_regional)))
      (S.disallow_right m0)
  in
  (m0, S.disallow_right m1)

let alloc_to_value_g2r (m0, m1) =
  let m0 =
    S.apply Alloc.obj0 Value.obj0
      (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Global_to_regional)))
      (S.disallow_left m0)
  in
  (m0, S.disallow_left m1)

let value_to_alloc_r2g (m0, m1) =
  let m0 =
    S.apply Value.obj0 Alloc.obj0
      (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Regional_to_global)))
      m0
  in
  (m0, m1)

let value_to_alloc_r2l (m0, m1) =
  let m0 =
    S.apply Value.obj0 Alloc.obj0
      (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Regional_to_local)))
      m0
  in
  (m0, m1)

