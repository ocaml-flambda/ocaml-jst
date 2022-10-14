(* TEST
   * expect *)
[@@@warning "+a"]

let f x y = x ^ y
[%%expect{|
val f : string -> string -> string = <fun>
|}]

let f_foo = f "foo" _
[%%expect{|
val f_foo : string -> local_ string = <fun>
|}]

let f_bar = f _ "bar"
[%%expect{|
val f_bar : string -> local_ string = <fun>
|}]

(* pre-existing behaviour, invalid in future *)
let f_foo = f "foo"
[%%expect{|
val f_foo : string -> string = <fun>
|}]

let f_err = f _ _ _
[%%expect{|
Line 1, characters 12-13:
1 | let f_err = f _ _ _
                ^
Error: This function has type string -> string -> string
       It is applied to too many arguments; maybe you forgot a `;'.
|}]

let f_err = (f _ _) _
[%%expect{|
val f_err : string -> local_ (string -> local_ string) = <fun>
|}]


let f_err = f "foo" "bar" "foo"
[%%expect{|
Line 1, characters 12-13:
1 | let f_err = f "foo" "bar" "foo"
                ^
Error: This function has type string -> string -> string
       It is applied to too many arguments; maybe you forgot a `;'.
|}]

let g ~x ~y = x ^ y
[%%expect{|
val g : x:string -> y:string -> string = <fun>
|}]


(* existing behaviour, invalid in future *)
let g_foo = g ~y:"foo"
[%%expect{|
val g_foo : x:string -> string = <fun>
|}]

let g_foo = g ~y:"foo" ~x:_
[%%expect{|
val g_foo : string -> local_ string = <fun>
|}]

let g_bar = g ~y:_ ~x:_
[%%expect{|
val g_bar : string -> string -> local_ string = <fun>
|}]

let g_err = g _ _ _
[%%expect{|
Line 1, characters 14-15:
1 | let g_err = g _ _ _
                  ^
Error: The function applied to this argument has type
         x:string -> y:string -> string
This argument cannot be applied without label
|}]

let g_err = g _ _
[%%expect{|
Line 1, characters 12-13:
1 | let g_err = g _ _
                ^
Warning 6 [labels-omitted]: labels x, y were omitted in the application of this function.
val g_err : string -> string -> local_ string = <fun>
|}]

let g_err = g ~x:"foo" ~y:"bar" _
[%%expect{|
Line 1, characters 12-13:
1 | let g_err = g ~x:"foo" ~y:"bar" _
                ^
Error: This function has type x:string -> y:string -> string
       It is applied to too many arguments; maybe you forgot a `;'.
|}]


(* testing side effects vs. partial application *)
let cell = ref ""

let f_eff ~x =
  cell := "x";
  fun ~y ->
    cell := "y";
    fun ~z ->
      cell := "z";
      x ^ y ^ z

[%%expect{|
val cell : string ref = {contents = ""}
val f_eff : x:string -> y:string -> z:string -> string = <fun>
|}]

let f_foo = f_eff ~x:"foo" ~y:_ ~z:"bar"
let _ = assert (!cell = "")
[%%expect{|
val f_foo : string -> local_ string = <fun>
- : unit = ()
|}]
(* FIXME: the above assertion should pass *)

(* testing locals vs. partial application *)
let bar (local_ _) =
  ();
  fun _ -> ()
[%%expect{|
val bar : local_ 'a -> ('b -> unit) = <fun>
|}]


let foo (local_ x) =
  let _  = bar x _ in
  ()
[%%expect{|
val foo : local_ 'a -> unit = <fun>
|}]
(* FIXME : with expected semantics and corresponding type checking,
   the above foo should NOT pass type check because x would be
   captured in the result of foo*)


(* note that in the following, labels are omitted, and order reversed  *)
let h ~x ~y ~z = (string_of_int x) ^ y ^ z
let h_foo = h ~y:_ ~x:_
[%%expect{|
val h : x:int -> y:string -> z:string -> string = <fun>
val h_foo : string -> int -> local_ (z:string -> string) = <fun>
|}]


(* An implementation based on naive syntax sugar unfolding would not play well
   with locals, because the added layer of function abstraction
   effectively creates another layer of region, which mess with locals and
   gives unexpected behaviours. Examples follow.
*)
let foo (local_ x) = x
let bar = foo _
[%%expect{|
val foo : local_ 'a -> local_ 'a = <fun>
val bar : 'a -> local_ 'a = <fun>
|}]

let foo (_) = local_
  let local_ x = "foo" in
  x
[%%expect{|
val foo : 'a -> local_ string = <fun>
|}]
let bar = foo _
[%%expect{|
val bar : 'a -> local_ string = <fun>
|}]
