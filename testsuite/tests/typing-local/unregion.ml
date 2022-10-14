(* TEST
 * expect *)

(* TYPING TESTS *)
(* TYPING TESTS *)
(* TYPING TESTS *)
(* the following two tests show that y is regional *)
let foo x =
  [%unregion] (
    let local_ y = None in
    (* y is not global *)
    ref y
  )
[%%expect{|
Line 5, characters 8-9:
5 |     ref y
            ^
Error: This value escapes its region
|}]

let foo x =
  [%unregion] (
    let local_ y = Some x in
    (* y is not local either *)
    (* because it can escape *)
    y
  )
[%%expect{|
val foo : 'a -> local_ 'a option = <fun>
|}]
(* note the type: RHS of arrow is local_,
   meaning it's indeed regional *)


let foo x =
  let local_ y = "foo" in
  [%unregion] (Some y)
[%%expect{|
Line 3, characters 20-21:
3 |   [%unregion] (Some y)
                        ^
Error: The value y is local, so cannot be used inside unregion
|}]

let foo x =
  let local_ y = "foo" in
  let z = [%unregion] (Some y) in
  z
[%%expect{|
Line 3, characters 10-30:
3 |   let z = [%unregion] (Some y) in
              ^^^^^^^^^^^^^^^^^^^^
Error: Unregion expression should only be in tail position
|}]

(* SEMANTICS TESTS *)
(* SEMANTICS TESTS *)
(* SEMANTICS TESTS *)
let foo x =
  [%unregion] (
    let local_ y = Some x in
    y
  );;

let bar _ =
  match foo 5 with
  | None -> "None!"
  | Some x -> "Some of " ^ (string_of_int (x + 0)) ;;
bar ();;
[%%expect{|
val foo : 'a -> local_ 'a option = <fun>
val bar : 'a -> string = <fun>
- : string = "Some of 5"
|}]
