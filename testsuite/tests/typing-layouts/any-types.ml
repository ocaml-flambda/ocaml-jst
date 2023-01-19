(* TEST
   * skip
   reason = "Unboxed types v5 not implemented yet"
   ** expect
*)

(* CR layouts (v5): enable this test *)

type 'a t1 = { f1 : #float; f2 : 'a }

[%%expect {|
success
|}]

type t2 = int t1
let x2 : t2 = { f1 = #3.; f2 = 4 }
let x2' = { f1 = #3.; f2 = 4 }

[%%expect {|
success
|}]

type t3 = #float t1
let x3 : t3 = { f1 = #3.; f2 = #4. }
let x3' = { f1 = #3.; f2 = #4. }

[%%expect {|
success
|}]

type t4 = #unit t1
let x4 : t4 = { f1 = #3.; f2 = #() }
let x4' = { f1 = #3.; f2 = #() }

[%%expect {|
success
|}]

let t5 = string t1

[%%expect {|
success, I think (but maybe not)
|}]

let x5 : t5 = { f1 = #3.; f2 = "hello" }

[%%expect {|
fail -- mixed-block restriction
|}]

let x5' = { f1 = #3.; f2 = "hello" }

[%%expect {|
fail -- mixed-block restriction
|}]

type ('a, 'b) t6 = { f1 : 'a; f2 : 'b }
type ('a, 'b) t7 = A of 'a * 'b

[%%expect {|
success
|}]

type t8 = (#float, int) t6
type t9 = (#float, int) t7

let x8 : t8 = { f1 : #1.; f2 = 2 }
let x8' = { f1 : #1.; f2 = 2 }

let x9 : t9 = A (#1., 2)
let x9' = A (#1., 2)

[%%expect {|
success
|}]

type t10 = (#float, string) t6
type t11 = (#float, string) t7

[%%expect {|
not sure; either is OK
|}]

let x10 : t10 = { f1 = #1.; f2 = "hello" }
let x11 : t11 = A (#1., "hello")

[%%expect {|
fail -- mixed-block restriction
|}]

let x10' = { f1 = #1.; f2 = "hello" }
let x11' = A (#1., "hello")

[%%expect {|
fail -- mixed-block restriction
|}]

type ('a, 'b, 'c) t12 = A of 'a * 'b | B of 'c

[%%expect {|
success
|}]

type t13 = (#float, #int64, string) t12
let x13 : t13 list = [A (#1., #2L); B "hello"]
let x13' = [A (#1., #2L); B "hello"]

[%%expect {|
success
|}]

let f x = A (#3., x)

[%%expect {|
success, but not sure what type we'll infer; there's no principal type
|}]
