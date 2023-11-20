(* TEST
   * skip
   reason = "Unboxed types v5 aren't implemented yet"
   ** expect
*)

(* CR layouts (v5): enable this test *)

let f () : #unit = #()
let g () = #()
let h #() = 5
let i #() = #()

[%%expect {|
success
|}]

let x =
  f ();
  g ();
  i #();
  5

[%%expect {|
success
|}]

let x : unit = box #()
let y : #unit = unbox ()

[%%expect {|
success
|}]

let x : unit = (box #() : #unit box)

[%%expect {|
success
|}]

type t : void = { f : #unit } [@@unboxed]

[%%expect {|
success
|}]

type t2 = (#unit : void)

[%%expect {|
success
|}]

module type Uunit = sig
  type t = #unit

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
end

module Uunit : Uunit = Uunit

[%%expect {|
success
|}]

let s = Uunit.to_string #()

[%%expect {|
success: "#()"
|}]

let b = Uunit.equal #() #()
let i = Uunit.compare #() #()

[%%expect {|
success: true, 0
|}]
