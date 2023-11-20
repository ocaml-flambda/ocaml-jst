(* TEST
   * skip
   reason = "Unboxed types v5 aren't implemented yet"
   ** expect
*)

(* CR layouts (v5): enable this test *)
(* CR layouts (v7): some of these tests change, because the mixed-block
   restriction should apply at construction, not type definition *)

(* records *)

type t1 = { f1 : #float; f2 : #int64; f3 : #float }
let x1 = { f1 = #1.; f2 = #2L; f3 = #3. }

[%%expect {|
success
|}]

type t2 = { f1 : #float; f2 : #int64; f3 : int }
(* ok because int is immediate *)
let x2 = { f1 = #1.; f2 = #2L; f3 = 3 }

[%%expect {|
success
|}]

type ('a : immediate) t2_2 = { f1 : #float; f2 : 'a }
let x2_2 = { f1 = #3.; f2 = true }

[%%expect {|
success
|}]

type 'a t2_3 = { f1 : #float; f2 : 'a }
let x2_3 = { f1 = #3.; f2 = true }

[%%expect {|
success: we should infer that 'a : any
|}]

let x2_3_bad = { f1 = #3.; f2 = "hello" }

[%%expect {|
fail -- mixed-block restriction or layout mismatch
|}]

type t3 = { f1 : #float; f2 : string }
let x3 = { f1 = #1.; f2 = "hello" }

[%%expect {|
fail -- mixed-block restriction
|}]

type enum = A | B | C | D
type t4 = { f1 : #float; f2 : #int64; f3 : enum }
let x4 = { f1 = #1.; f2 = #2L; f3 = C }

[%%expect {|
success
|}]

type not_enum = A | B | C | D of int
type t5 = { f1 : #float; f2 : #int64; f3 : not_enum }
let x5 = { f1 = #1.; f2 = #2L; f3 = C }

[%%expect {|
fail
|}]

type t6 = { f1 : #float; f2 : #int64; f3 : #unit; f4 : #unit }
let x6 = { f1 = #1.; f2 = #2L; f3 = #(); f4 = #() }

[%%expect {|
success
|}]

type t7 = { f1 : string; f2 : int option; f3 : #unit }
let x7 = { f1 = "hello"; f2 = None; f3 = #() }

[%%expect {|
success
|}]

type ('a : immediate) imm_t
type t8 = { f1 : #unit; f2 : #unit }
let x8 = { f1 = #(); f2 = #() }
type t8_ = t8 imm_t

[%%expect {|
success
|}]

type t9 = { f1 : int; f2 : #unit; f3 : #unit } [@@unboxed]
let x9 = { f1 = 1; f2 = #(); f3 = #() }
type t10 = t9 imm_t

[%%expect {|
success would be nice, but maybe in a future version
|}]

(* variants *)

type t11 = A of #int64 | B of #float | C of string | D
let x11_1 = A #1L
let x11_2 = B #2.
let x11_3 = C "hello"
let x11_4 = D

[%%expect {|
success
|}]

type t12 = A of #int64 * #float | B of int * string
let x12_1 = A (#1L, #2.)
let x12_2 = B (3, "four")

[%%expect {|
success
|}]

type t13 = A of #int64 * string | B of float
let x13_1 = A (#1L, "two")
let x13_2 = B #3.

[%%expect {|
fail -- mixed-block restriction
|}]

type t14 = A of #float * #unit * #unit | B of string * #unit
let x14_1 = A (#1., #(), #())
let x4_2 = B ("two", #())

[%%expect {|
success
|}]

type t15 = A of #float * int | B of string * int
let x15_1 = A (#1., 2)
let x15_2 = B ("three", 4)

[%%expect {|
success
|}]

type t16 = A of #unit | B | C of #unit * #unit
let x16_1 = A #()
let x16_2 = B
let x16_3 = C (#(), #())
type t17 = t16 imm_t

[%%expect {|
success
|}]

(* tuples *)

type t18 = #int16 * #int32
let x18 : t18 = #1s, #2l

[%%expect {|
success
|}]

type t19 = #float * #float * #unit
let x19 : t19 = #1., #2., #()

[%%expect {|
success
|}]

let x20 = #1b, #2s, #3l, #4L, #5n, #6., #()

[%%expect {|
success
|}]

let x21 = #1b, #2s, #3l, #4L, (#5n, #6., #())

[%%expect {|
fail -- mixed-block restriction
|}]

type 'a t22 = #float * #int64 * 'a

[%%expect {|
not sure: what's the layout of 'a?
  could be `any`, with the mixed-block restriction checked on construction
|}]

(* modules *)

module M1 = struct
  let x = #42L
end

[%%expect {|
success
|}]

module M2 = struct
  let x = #32L
  let y = #3.14
  let z = #()
end

[%%expect {|
success
|}]

module M3 = struct
  let x = #32L
  let y = "hello"
end

[%%expect {|
fail -- mixed-block restriction
|}]

module M4 = struct
  let x = #32L
  let y = "hello"
  let x = 32
end

[%%expect {|
success: the module doesn't actually store anything unboxed
|}]

