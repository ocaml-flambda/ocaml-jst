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


(* in the following, f_eff is not evaluated at all *)
let f_foo = f_eff ~x:"foo" ~y:_ ~z:"bar"
let _ = assert (!cell = "")
[%%expect{|
val f_foo : string -> local_ string = <fun>
- : unit = ()
|}]


(* Once recognized as partial applicaiton, 
even the specified arguments are not evaluated.
   *)
let cell = ref ""
let foo x y = x ^ y
let bar = foo _ (cell := "a"; "foo")
let _ = assert (!cell = "")
[%%expect{|
val cell : string ref = {contents = ""}
val foo : string -> string -> string = <fun>
val bar : string -> local_ string = <fun>
- : unit = ()
|}]

(* This is unfortunately inconsistent with 
the other pre-existing behaviours such as 
currying and omitted labeled arguments. 
This can be fixed by changing the sugar 
(add some let bindings)
*)
 let cell = ref ""
 let foo ~x ~y = x ^ y
 let bar = foo ~y:(cell := "a"; "foo")
 let _  = assert (!cell = "")
 [%%expect{|
val cell : string ref = {contents = ""}
val foo : x:string -> y:string -> string = <fun>
val bar : x:string -> string = <fun>
Exception: Assert_failure ("", 4, 10).
|}]


(* Note that in the following, labels are omitted, and the order is reversed  *)
(* Alternative design choice is to preserve the labels. 
   not hard to switch to that *)
let h ~x ~y ~z = (string_of_int x) ^ y ^ z
let h_foo = h ~y:_ ~x:_
[%%expect{|
val h : x:int -> y:string -> z:string -> string = <fun>
val h_foo : string -> int -> local_ (z:string -> string) = <fun>
|}]

(* An implementation based on naive syntax sugar unfolding would not play well
   with locals, because the added layer of function abstraction
   effectively creates another layer of region, which mess with locals and
   gives unexpected behaviours. Our syntax sugar uses [%unregion] under the hood 
   to avoid this issue. Examples follow.
*)

let foo (local_ x) = x
module M : sig
  val bar : local_ 'a -> local_ 'a
end = struct
  let bar = foo _
end 
[%%expect{|
val foo : local_ 'a -> local_ 'a = <fun>
module M : sig val bar : local_ 'a -> local_ 'a end
|}]

let foo (_) = local_
  let local_ x = "foo" in
  x

let bar = foo _  
[%%expect{|
val foo : 'a -> local_ string = <fun>
val bar : 'a -> local_ string = <fun>
|}]
