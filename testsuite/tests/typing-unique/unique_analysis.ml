(* TEST
   flags += "-extension unique"
 * expect *)

(* This file is mostly to test the uniqueness analysis *)

let unique_id : 'a. unique_ 'a -> unique_ 'a = fun x -> x
[%%expect{|
val unique_id : unique_ 'a -> unique_ 'a = <fun>
|}]

let shared_id : 'a -> 'a = fun x -> x
[%%expect{|
val shared_id : 'a -> 'a = <fun>
|}]

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


let branching (unique_ x : float) = unique_ if true then x else x
[%%expect{|
val branching : unique_ float -> float = <fun>
|}]

(* whether we constrain uniqueness or linearity is irrelavant
   for testing uniqueness analysis. Therefore, in the rest we
   will only constrain uniqueness *)
let branching (once_ x : float) = if true then x else x
[%%expect{|
val branching : once_ float -> once_ float = <fun>
|}]

let branching b =
  let unique_ r = { x = 23 } in
  if b then update r
       else update r
[%%expect{|
val branching : bool -> box = <fun>
|}]

let sequence (unique_ x : float) = unique_ let y = x in (x, y)
[%%expect{|
Line 1, characters 60-61:
1 | let sequence (unique_ x : float) = unique_ let y = x in (x, y)
                                                                ^
Error: y is used uniquely here so cannot be used twice. It will be used again at:
Line 1, characters 57-58:
1 | let sequence (unique_ x : float) = unique_ let y = x in (x, y)
                                                             ^
  y was used because x is an alias of y.
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

let children_unique (unique_ xs : float list) = match xs with
  | [] -> (0., [])
  | x :: xx -> unique_ (x, xx)
[%%expect{|
val children_unique : unique_ float list -> float * float list = <fun>
|}]

let borrow_match (unique_ fs : 'a list) = unique_ match fs with
  | [] -> []
  | x :: xs as gs -> gs
[%%expect{|
val borrow_match : unique_ 'a list -> 'a list = <fun>
|}]

let borrow_match (unique_ fs : 'a list) = unique_ match fs with
    | [] -> []
    | x :: xs -> fs
[%%expect{|
val borrow_match : unique_ 'a list -> 'a list = <fun>
|}]

let dup_child (unique_ fs : 'a list) = unique_ match fs with
  | [] -> ([], [])
  | x :: xs as gs -> (gs, xs)
[%%expect{|
Line 3, characters 22-24:
3 |   | x :: xs as gs -> (gs, xs)
                          ^^
Error: gs is used uniquely here so cannot be used twice. It was used previously at:
Line 3, characters 26-28:
3 |   | x :: xs as gs -> (gs, xs)
                              ^^
  gs was used because xs is a child of gs.
|}]


let or_patterns1 : unique_ float list -> float list -> float = fun x y -> match x, y with
  | z :: _, _ | _, z :: _ -> unique_ z
  | _, _ -> 42.0
[%%expect{|
Line 2, characters 37-38:
2 |   | z :: _, _ | _, z :: _ -> unique_ z
                                         ^
Error: Found a shared value where a unique value was expected
|}]

let or_patterns2 : float list -> unique_ float list -> float = fun x y -> match x, y with
  | z :: _, _ | _, z :: _ -> unique_ z
  | _, _ -> 42.0
[%%expect{|
Line 2, characters 37-38:
2 |   | z :: _, _ | _, z :: _ -> unique_ z
                                         ^
Error: Found a shared value where a unique value was expected
|}]

let or_patterns3 p =
  let unique_ x = 3 in let unique_ y = 4 in
  match p, x, y with
  | true, z, _ | false, _, z -> let _ = unique_id z in unique_id y
[%%expect{|
Line 4, characters 50-51:
4 |   | true, z, _ | false, _, z -> let _ = unique_id z in unique_id y
                                                      ^
Error: z is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 65-66:
4 |   | true, z, _ | false, _, z -> let _ = unique_id z in unique_id y
                                                                     ^
  z was used because y is an alias of z.
|}]

let or_patterns4 p =
  let unique_ x = 3 in let unique_ y = 4 in
  match p, x, y with
  | true, z, _ | false, _, z -> let _ = unique_id x in unique_id y
[%%expect{|
val or_patterns4 : bool -> int = <fun>
|}]

let or_patterns5 p =
  let unique_ x = 3 in let unique_ y = 4 in
  match p, x, y with
  | true, z, _ | false, _, z -> let _ = unique_id z in unique_id x
[%%expect{|
Line 4, characters 50-51:
4 |   | true, z, _ | false, _, z -> let _ = unique_id z in unique_id x
                                                      ^
Error: z is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 65-66:
4 |   | true, z, _ | false, _, z -> let _ = unique_id z in unique_id x
                                                                     ^
  z was used because x is an alias of z.
|}]

let mark_top_shared =
  let unique_ xs = 2 :: 3 :: [] in
  match xs with
  | x :: xx ->
      let _ = unique_id xs in
      unique_ xx
  | [] -> []
[%%expect{|
Line 5, characters 24-26:
5 |       let _ = unique_id xs in
                            ^^
Error: xs is used uniquely here so cannot be used twice. It will be used again at:
  xs was used because xx is a child of xs.
|}]

let mark_top_shared =
  let unique_ xs = 2 :: 3 :: [] in
  let _ = unique_id xs in
  match xs with
  | x :: xx -> unique_ xx
  | [] -> []
[%%expect{|
Line 3, characters 20-22:
3 |   let _ = unique_id xs in
                        ^^
Error: xs is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 8-10:
4 |   match xs with
            ^^

|}]

let mark_shared_in_one_branch b x =
  if b then unique_id (x, 3.0)
       else (x, x)
[%%expect{|
val mark_shared_in_one_branch : bool -> unique_ float -> float * float =
  <fun>
|}]

let mark_shared_in_one_branch b x =
  if b then (x, x)
       else unique_id (x, 3.0)
[%%expect{|
val mark_shared_in_one_branch : bool -> unique_ float -> float * float =
  <fun>
|}]

let expr_tuple_match f x y =
  match f x, y with
  | (a, b), c -> unique_ (a, c)
[%%expect{|
val expr_tuple_match : ('a -> unique_ 'b * 'c) -> 'a -> unique_ 'd -> 'b * 'd =
  <fun>
|}]

let expr_tuple_match f x y =
  match f x, y with
  | (a, b) as t, c -> let d = unique_id t in unique_ (c, d)
[%%expect{|
val expr_tuple_match :
  ('a -> unique_ 'b * 'c) -> 'a -> unique_ 'd -> 'd * ('b * 'c) = <fun>
|}]

let expr_tuple_match f x y =
  match f x, y with
  | (a, b) as t, c -> let d = unique_id t in unique_ (a, d)
[%%expect{|
Line 3, characters 40-41:
3 |   | (a, b) as t, c -> let d = unique_id t in unique_ (a, d)
                                            ^
Error: t is used uniquely here so cannot be used twice. It will be used again at:
Line 3, characters 54-55:
3 |   | (a, b) as t, c -> let d = unique_id t in unique_ (a, d)
                                                          ^
  t was used because a is a child of t.
|}]

let tuple_parent_marked a b =
  match (a, b) with
  | (_, b) as _t -> shared_id b
[%%expect{|
val tuple_parent_marked : 'a -> 'b -> 'b = <fun>
|}]

let tuple_parent_marked a b =
  match (a, b) with
  | (true, b') -> unique_id b'
  | (false, b') as _t -> shared_id b'
[%%expect{|
Line 2, characters 12-13:
2 |   match (a, b) with
                ^
Error: b is used uniquely here so cannot be used twice (_t refers to a tuple containing it). It will be used again at:
Line 3, characters 28-30:
3 |   | (true, b') -> unique_id b'
                                ^^
  b was used because b' is an alias of b.
|}]

let tuple_parent_marked a b =
  match (a, b) with
  | (false, b) as _t -> shared_id b
  | (true, b) -> unique_id b
[%%expect{|
Line 2, characters 12-13:
2 |   match (a, b) with
                ^
Error: b is used uniquely here so cannot be used twice (_t refers to a tuple containing it). It will be used again at:
Line 4, characters 27-28:
4 |   | (true, b) -> unique_id b
                               ^

|}]

let unique_match_on a b =
  let unique_ t = (a, b) in t
[%%expect{|
val unique_match_on : unique_ 'a -> unique_ 'b -> 'a * 'b = <fun>
|}]

type ('a, 'b) record = { foo : 'a; bar : 'b }
[%%expect{|
type ('a, 'b) record = { foo : 'a; bar : 'b; }
|}]

let unique_match_on a =
  let _p = { unique_ a.foo with foo = (); bar = () } in
  match a with
  | { bar } -> bar
[%%expect{|
val unique_match_on : unique_ (('a, 'b) record, 'c) record -> 'c = <fun>
|}]

let unique_match_on a =
  let _p = { unique_ a.foo with foo = (); bar = () } in
  match a with
  | { foo; bar } -> (foo, bar)
[%%expect{|
Line 2, characters 21-26:
2 |   let _p = { unique_ a.foo with foo = (); bar = () } in
                         ^^^^^
Error: a.foo is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 21-24:
4 |   | { foo; bar } -> (foo, bar)
                         ^^^
  a.foo was used because foo is a parent of a.foo.
|}]

let unique_match_on a =
  let _p = { unique_ a.foo with foo = (); bar = () } in
  match a with
  | { foo = { foo }; bar } -> (foo, bar)
[%%expect{|
Line 2, characters 21-26:
2 |   let _p = { unique_ a.foo with foo = (); bar = () } in
                         ^^^^^
Error: a.foo is used uniquely here so cannot be used twice. It will be used again at:
Line 3, characters 8-9:
3 |   match a with
            ^
  a.foo was used because a is an alias of a.foo.
|}]

let match_function : unique_ 'a * 'b -> 'a * ('a * 'b) = function
  | (a, b) as t -> unique_ (a, t)
[%%expect{|
Line 2, characters 31-32:
2 |   | (a, b) as t -> unique_ (a, t)
                                   ^
Error: t is used uniquely here so cannot be used twice. It will be used again at:
Line 2, characters 28-29:
2 |   | (a, b) as t -> unique_ (a, t)
                                ^
  t was used because a is a child of t.
|}]

let tuple_parent_marked a b =
  match (a, b) with
  | (a, b) as t -> unique_ (a, t)
[%%expect{|
Line 3, characters 31-32:
3 |   | (a, b) as t -> unique_ (a, t)
                                   ^
Error: t is used uniquely here so cannot be used twice. It will be used again at:
Line 3, characters 28-29:
3 |   | (a, b) as t -> unique_ (a, t)
                                ^
  t was used because a is a child of t.
|}]

(* CR-someday anlorenzen: This one shouldn't fail in a more clever analysis. *)
let or_patterns6 flag f x y =
  match flag, f x, y with
  | true, a, (_, b) | false, b, (_, a) -> (unique_id a, unique_id b)
[%%expect{|
Line 3, characters 66-67:
3 |   | true, a, (_, b) | false, b, (_, a) -> (unique_id a, unique_id b)
                                                                      ^
Error: b is used uniquely here so cannot be used twice. It will be used again at:
Line 3, characters 53-54:
3 |   | true, a, (_, b) | false, b, (_, a) -> (unique_id a, unique_id b)
                                                         ^
  b was used because a is an alias of b.
|}]


type point = { dim : int; x : float; y : float; z : float }
[%%expect{|
type point = { dim : int; x : float; y : float; z : float; }
|}]

let record_mode_vars (p : point) =
  let x = unique_id p.x in
  let y = (p.y, p.y) in
  (x, y, unique_ p.z)
[%%expect{|
val record_mode_vars : unique_ point -> float * (float * float) * float =
  <fun>
|}]

let record_mode_vars (p : point) =
  let x = unique_id p.x in
  let y = (p.x, p.y) in
  (x, y, unique_ p.z)
[%%expect{|
Line 2, characters 20-23:
2 |   let x = unique_id p.x in
                        ^^^
Error: p.x is used uniquely here so cannot be used twice. It will be used again at:
Line 3, characters 11-14:
3 |   let y = (p.x, p.y) in
               ^^^

|}]

let record_mode_vars (p : point) =
  let y = (p.x, p.y) in
  let x = unique_id p.x in
  (x, y, unique_ p.z)
[%%expect{|
Line 3, characters 20-23:
3 |   let x = unique_id p.x in
                        ^^^
Error: p.x is used uniquely here so cannot be used twice. It was used previously at:
Line 2, characters 11-14:
2 |   let y = (p.x, p.y) in
               ^^^
  p.x was used because y refers to a tuple containing it.
|}]

let record_mode_vars (p : point) =
  let p2 = { unique_ p with x = 4.0 } in
  let x = p.x in
  (x, p2)
[%%expect{|
Line 2, characters 21-22:
2 |   let p2 = { unique_ p with x = 4.0 } in
                         ^
Error: p is used uniquely here so cannot be used twice. It will be used again at:
Line 3, characters 10-11:
3 |   let x = p.x in
              ^

|}]