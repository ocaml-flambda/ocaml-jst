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

type tree = Leaf | Node of tree * tree
let rec make_tree = fun n ->
  if n <= 0 then Leaf
  else let unique_ x = make_tree (n - 1)
       in Node (x, x)
[%%expect{|
type tree = Leaf | Node of tree * tree
Line 5, characters 19-20:
5 |        in Node (x, x)
                       ^
Error: x is used uniquely here so cannot be used twice. It will be used again at:
Line 5, characters 16-17:
5 |        in Node (x, x)
                    ^

|}]

let call_many (unique_ x) =
  let foo () = unique_ (x + 1) in
  ((unique_ foo ()), unique_ foo ())
[%%expect{|
Line 2, characters 23-30:
2 |   let foo () = unique_ (x + 1) in
                           ^^^^^^^
Error: Found a shared value where a unique value was expected
|}]

let loop =
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

let loop =
  let f (unique_ a) = a in
  for i = 0 to 5 do
    let unique_ a = 3 in
    let _ = f a in ()
  done;
  ()
[%%expect{|
val loop : unit = ()
|}]

let borrow (unique_ x) (unique_ y) =
  if x < y then unique_ (x, y) else unique_ (y, x)
[%%expect{|
Line 2, characters 28-29:
2 |   if x < y then unique_ (x, y) else unique_ (y, x)
                                ^
Error: y is used uniquely here so cannot be used twice. It was used previously at:
Line 2, characters 9-10:
2 |   if x < y then unique_ (x, y) else unique_ (y, x)
             ^

|}]

let borrow cmp x y =
  if cmp (borrow_ x) (borrow_ y) < 0 then unique_ (x, y) else unique_ (y, x)
[%%expect{|
val borrow :
  (local_ 'a -> (local_ 'a -> int)) -> unique_ 'a -> (unique_ 'a !-> 'a * 'a) =
  <fun>
|}]

let borrow : unique_ 'a -> (local_ 'a -> unique_ 'b) -> unique_ ('b * 'a) = fun x f ->
  let z = f (borrow_ x) in (z, x)
[%%expect{|
val borrow : unique_ 'a -> (local_ 'a -> unique_ 'b) -> unique_ 'b * 'a =
  <fun>
|}]

let return_local : local_ 'a -> local_ 'a = fun x -> x
let return_global : local_ 'a -> int = fun x -> 0
[%%expect{|
val return_local : local_ 'a -> local_ 'a = <fun>
val return_global : local_ 'a -> int = <fun>
|}]

let foo x =
  let _y = return_global (return_local (borrow_ x)) in
  unique_ x
[%%expect{|
Line 2, characters 48-49:
2 |   let _y = return_global (return_local (borrow_ x)) in
                                                    ^
Error: The borrowed value x escapes as its context returns a local value. Its context is:
Line 2, characters 25-51:
2 |   let _y = return_global (return_local (borrow_ x)) in
                             ^^^^^^^^^^^^^^^^^^^^^^^^^^

|}]


let foo x =
  let _y =
    let z = borrow_ x in
    return_global (return_local z) in
  unique_ x
[%%expect{|
val foo : unique_ 'a -> 'a = <fun>
|}]

let foo x =
  let local_ _y = (* y is local... but bound to a global value! *)
    let z = borrow_ x in
    return_global (return_local z) in
  unique_ x
[%%expect{|
val foo : unique_ 'a -> 'a = <fun>
|}]











