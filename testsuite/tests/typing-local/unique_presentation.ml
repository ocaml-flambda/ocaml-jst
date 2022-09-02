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
  let _s = update r in
  let t = update r in
  t
[%%expect{|
Line 3, characters 18-19:
3 |   let _s = update r in
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

let curry (unique_ b1 : box) (unique_ b2 : box) = b1
[%%expect{|
val curry : unique_ box -> (unique_ box !-> box) = <fun>
|}]

let curry : unique_ box -> (unique_ box !-> unique_ box) = fun b1 b2 -> b1
[%%expect{|
val curry : unique_ box -> (unique_ box !-> unique_ box) = <fun>
|}]

let curry : unique_ box -> (unique_ box -> unique_ box) = fun b1 b2 -> b1
[%%expect{|
Line 1, characters 58-73:
1 | let curry : unique_ box -> (unique_ box -> unique_ box) = fun b1 b2 -> b1
                                                              ^^^^^^^^^^^^^^^
Error: This function captures a unique value and so its type needs
       to use the !-> arrow. This ensures that the function is only called once.
|}]

let loop : unit =
  let unique_ a = 3 in
  let f (unique_ a) = a in
  for i = 0 to 5 do
    let _ = f a in ()
  done;
  ()
[%%expect{|
Line 5, characters 14-15:
5 |     let _ = f a in ()
                  ^
Error: Found a shared value where a unique value was expected
  Hint: This identifier cannot be used uniquely,
  because it was defined outside of the for-loop.
|}]

let loop : unit =
  let f (unique_ a) = a in
  for i = 0 to 5 do
    let unique_ a = 3 in
    let _ = f a in ()
  done;
  ()
[%%expect{|
val loop : unit = ()
|}]
