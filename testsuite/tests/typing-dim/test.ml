module Dim : sig
  type 'a dfloat = private float
  val create : float ->  <'a> dfloat
  val (+:) : <'a> dfloat -> <'a> dfloat -> <'a> dfloat
  val ( *: ) : <'a> dfloat ->  <'b> dfloat -> <'a * 'b> dfloat
  val ( /: ) : <'a> dfloat ->  <'b> dfloat -> <'a / 'b> dfloat
  val inv :  <'a> dfloat -> <1 / 'a> dfloat
  val dsqrt : <'a ^ 2> dfloat -> <'a> dfloat
end = struct

  type 'a dfloat = float

  let create f = f
  let ( +: ) = ( +. )
  let ( *: ) = ( *. )
  let ( /: ) = ( /. )
  let inv f = 1. /. f
  let dsqrt = sqrt
end
;;

open Dim;;
type dlist = <l> list;;
let x : <m> dfloat = create 3.;;
let y : <m> dfloat = create 4.;;
let _ = (x = y);;

let div : <'a> dfloat -> <'a * 'b> dfloat -> <1 / 'b> dfloat = ( /: );;
let lcm (x: 'a dfloat) (y: 'b dfloat) (z: 'c dfloat) =
  (x *: x) +: (y *: y *: y) +: (z *: z *: z *: z *: z);;
let lcm_bis x y z =
  (x *: x) +: (y *: y *: y) +: (z *: z *: z *: z *: z);;

(* polymorphic recursion *)
let rec prodlist:
    'a 'b. <'a> dfloat list -> <'b> dfloat list -> <'a*'b> dfloat list =
  fun  x y -> match x,y with
  | [],_ | _, [] -> []
  | (x::xs,y::ys) -> (x *: y) :: (prodlist ys xs);;

let f (x : 'a option) : <'a> dfloat option = None;;
f (Some 1);; (* fail: bad unit variable *)

(* fail: incompatible *)
module M : sig val v : <m> dfloat end =
  struct let v : <k> dfloat = create 1. end;;


(* success: 'c can be instantiated with 1 *)
module M =
  struct
    let x : <'c> dfloat = create 1.0
    let f : <'a> dfloat -> <'a^2 / 'b^2 * 'c> dfloat -> <'b> dfloat =
      fun _ _ ->
        let y : <'c> dfloat = x in ignore y; create 1.0
  end;;
module M' : sig val f : <'a> dfloat -> <1> dfloat -> <'a> dfloat end = M;;

(* fail: non-generalizable 'c cannot be instantiated with outside 'a *)
module M =
  struct
    let x : <'c> dfloat = create 1.0
    let f : <'a> dfloat -> <'a^2 / 'b * 'c> dfloat -> <'b> dfloat =
      fun _ _ ->
        let y : <'c> dfloat = x in ignore y; create 1.0
  end;;
module M' : sig val f : <'a> dfloat -> <1> dfloat -> <'a> dfloat end = M;;

(* fail: outside 'a cannot be instantiated with <m> *)
module M =
  struct
    let x : <'c> dfloat = create 1.0
    let f : <'a> dfloat -> <'a^2 / 'b * 'c> dfloat -> <m> dfloat =
      fun _ _ ->
        let y : <'c> dfloat = x in ignore y; create 1.0
  end;;
module M' : sig val f : <'a> dfloat -> <1> dfloat -> <'a> dfloat end = M;;

(* Some more examples *)
let g : <m * s ^ -2> dfloat = create 9.8;;
let speed (t : <s> dfloat) = t *: g;;

let foot : <m/ft> dfloat = create 0.305;;
let feet_to_meters (x : <ft> dfloat) = x *: foot;;
