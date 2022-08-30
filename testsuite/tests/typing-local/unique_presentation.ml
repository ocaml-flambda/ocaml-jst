(* TEST
   flags += "-extension unique"
 * expect *)


type box = { x : int }
[%%expect{|
type box = { x : int; }
|}]

let update : unique_ box -> unique_ box = fun r ->
  if r.x == 42 then { unique_ r with x = 11 }
  else { unique_ r with x = 42 }
[%%expect{|
val update : unique_ box -> unique_ box = <fun>
|}]

let sequence =
  let r = { x = 23 } in
  let s = update r in
  let t = update s in
  t
[%%expect{|
val sequence : box = {x = 11}
|}]

let sequence =
  let r = { x = 23 } in
  let s = update r in
  let t = update r in
  (s, t)
[%%expect{|
Line 3, characters 17-18:
3 |   let s = update r in
                     ^
Error: r is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 17-18:
4 |   let t = update r in
                     ^

|}]

let branching b =
  let unique_ r = { x = 23 } in
  if b then update r
       else update r
[%%expect{|
val branching : bool -> box = <fun>
|}]

let tail_unique : 'a. unique_ 'a list -> unique_ 'a list = function
  | [] -> []
  | _ :: xx -> xx
[%%expect{|
val tail_unique : unique_ 'a list -> unique_ 'a list = <fun>
|}]

let curry : 'a. unique_ box -> (unique_ box -> unique_ box) = fun b1 b2 -> b1
[%%expect{|
Line 1, characters 75-77:
1 | let curry : 'a. unique_ box -> (unique_ box -> unique_ box) = fun b1 b2 -> b1
                                                                               ^^
Error: Found a shared value where a unique value was expected
|}, Principal{|
Line 1, characters 69-77:
1 | let curry : 'a. unique_ box -> (unique_ box -> unique_ box) = fun b1 b2 -> b1
                                                                         ^^^^^^^^
Error: This expression has type unique_ 'a -> box
       but an expression was expected of type unique_ box -> unique_ box
|}]
