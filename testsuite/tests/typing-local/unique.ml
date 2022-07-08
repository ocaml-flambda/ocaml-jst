(* TEST
 * expect *)

type 'a glob = { global_ glob: 'a } [@@unboxed]
[%%expect{|
type 'a glob = { global_ glob : 'a; } [@@unboxed]
|}]

let dup (unique_ x) = (x, x)
[%%expect{|
val dup : unique_ 'a -> 'a * 'a = <fun>
|}]

let dup (unique_ x) = unique_ (x, x)
[%%expect{|
  Error: two uses of unique_ var
|}]

let dup (glob : 'a) : 'a glob * 'a glob = unique_ ({glob}, {glob})
[%%expect{|
val dup : 'a -> unique_ 'a glob * 'a glob = <fun>
|}]

let drop (unique_ x) = unique_ ()
[%%expect{|
val drop : unique 'a -> unit = <fun>
|}]

let branching (unique_ x : float) = unique_ if true then x else x
[%%expect{|
val branching : unique_ float -> unique_ float = <fun>
|}]

let sequence (unique_ x : float) = unique_ let y = x in x
[%%expect{|
Error: variable x used twice
|}]

let children_unique (unique_ xs : float list) = unique_ match xs with
  | [] -> (0., [])
  | x :: xx -> (x, xx)
[%%expect{|
val children_unique : unique_ float list -> unique_ float * float list = <fun>
|}]

let borrow_match (unique_ fs : 'a list) = unique_ match fs with
  | [] -> []
  | x :: xs as gs -> gs
[%%expect{|
val borrow_match : unique_ 'a list -> unique_ 'a list = <fun>
|}]

let dup_child (unique_ fs : 'a list) = unique_ match fs with
  | [] -> ([], [])
  | x :: xs as gs -> (gs, xs)
[%%expect{|
  Error: gs and xs can not be unique at the same time
|}]

let unique_id (unique_ x) = unique_ x
[%%expect{|
val unique_id : unique_ 'a -> unique_ 'a = <fun>
|}]

(* This case is interesting because it fails for locals but should not fail for uniques *)
let tail_unique _x =
  let unique_ y = 1.0 in unique_id y
[%%expect{|
val tail_unique : unique_ 'a -> unique_ float = <fun>
|}]

let higher_order (unique_ x : 'a) (f : unique_ 'a -> unique_ 'b) = unique_ f x
[%%expect{|
val higher_order : unique_ 'a -> (unique_ 'a -> unique_ 'b) -> unique_ 'b = <fun>
|}]

let higher_order2 (x : 'a) (f : 'a -> unique_ 'b) = unique_ f x
[%%expect{|
val higher_order2 : 'a -> ('a -> unique_ 'b) -> unique_ 'b = <fun>
|}]

let higher_order3 (unique_ x : 'a) (f : 'a -> 'b) = unique_ f x
[%%expect{|
Error: result of f x is not unique
|}]

let higher_order4 (x : 'a) (f : unique_ 'a -> 'b) = f x
[%%expect{|
Error: Argument x to f is not unique
|}]

let higher_order5 (unique_ x) = let f (unique_ x) = unique_ x in higher_order x f
[%%expect{|
val higher_order5 : unique_ 'a -> unique_ 'a
|}]

let higher_order6 (unique_ x) = let f (unique_ x) = unique_ x in higher_order2 x f
[%%expect{|
Error: Expected ('a -> unique_ 'b) but got (unique_ 'a -> unique_ 'b)
|}]

type record_update = { x : int }
[%%expect{|
type record_update = { x : int; }
|}]

let update (unique_ r : record_update) = unique_ { unique_ r with x = 1 }
[%%expect{|
val update : unique_ record_update -> unique_ record_update = <fun>
|}]

let inf1 (unique_ x : float) = unique_ let y = x in y
[%%expect{|
val inf1 : unique_ float -> unique_ float
|}]

let inf2 (b : bool) (unique_ x : float) = unique_ let y = if b then x else 1.0 in y
[%%expect{|
val inf2 : bool -> unique_ float -> unique_ float
|}]

let inf3 (b : bool) (unique_ x : float) (y : float) = unique_ let z = if b then x else y in z
[%%expect{|
  Error: z is not unique
|}]

let inf4 (unique_ x) = let f x = x in higher_order x f
[%%expect{|
val inf4 : unique_ 'a -> unique_ 'a
|}]
