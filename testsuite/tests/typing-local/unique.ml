(* TEST
   flags += "-extension unique"
 * expect *)

type 'a glob = { global_ glob: 'a } [@@unboxed]
[%%expect{|
type 'a glob = { global_ glob : 'a; } [@@unboxed]
|}]

let dup (unique_ x) = (x, x)
[%%expect{|
val dup : unique_ 'a -> 'a * 'a = <fun>
|}]

let dup x = unique_ (x, x)
[%%expect{|
Line 1, characters 24-25:
1 | let dup x = unique_ (x, x)
                            ^
Error: x is used uniquely here so cannot be used twice. It will be used again at:
Line 1, characters 21-22:
1 | let dup x = unique_ (x, x)
                         ^

|}]

let dup (glob : 'a) : 'a glob * 'a glob = unique_ ({glob}, {glob})
[%%expect{|
val dup : 'a -> 'a glob * 'a glob = <fun>
|}]

module M : sig
  val drop : unique_ 'a -> unique_ unit
  end = struct
  let drop (unique_ x) = unique_ ()
end
[%%expect{|
module M : sig val drop : unique_ 'a -> unique_ unit end
|}]

let branching (unique_ x : float) = unique_ if true then x else x
[%%expect{|
val branching : unique_ float -> float = <fun>
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

let unique_id : 'a. unique_ 'a -> unique_ 'a = fun x -> x
[%%expect{|
val unique_id : unique_ 'a -> unique_ 'a = <fun>
|}]

let shared_id : 'a -> 'a = fun x -> x
[%%expect{|
val shared_id : 'a -> 'a = <fun>
|}]

(* This case is interesting because it fails for locals but should not fail for uniques *)
let tail_unique _x =
  let unique_ y = 1.0 in unique_id y
[%%expect{|
val tail_unique : 'a -> float = <fun>
|}]

let higher_order (f : unique_ 'a -> unique_ 'b) (unique_ x : 'a) = unique_ f x
[%%expect{|
val higher_order : (unique_ 'a -> unique_ 'b) -> unique_ 'a -> 'b = <fun>
|}]

let higher_order2 (f : 'a -> unique_ 'b) (x : 'a) = unique_ f x
[%%expect{|
val higher_order2 : ('a -> unique_ 'b) -> 'a -> 'b = <fun>
|}]

let higher_order3 (f : 'a -> 'b) (unique_ x : 'a) = unique_ f x
[%%expect{|
Line 1, characters 60-63:
1 | let higher_order3 (f : 'a -> 'b) (unique_ x : 'a) = unique_ f x
                                                                ^^^
Error: Found a shared value where a unique value was expected
|}]

let higher_order4 (f : unique_ 'a -> 'b) (x : 'a) = f (shared_id x)
[%%expect{|
Line 1, characters 54-67:
1 | let higher_order4 (f : unique_ 'a -> 'b) (x : 'a) = f (shared_id x)
                                                          ^^^^^^^^^^^^^
Error: Found a shared value where a unique value was expected
|}]

let higher_order5 (unique_ x) = let f (unique_ x) = unique_ x in higher_order f x
[%%expect{|
val higher_order5 : unique_ 'a -> 'a = <fun>
|}]

let higher_order6 (unique_ x) = let f (unique_ x) = unique_ x in higher_order2 f x
[%%expect{|
Line 1, characters 79-80:
1 | let higher_order6 (unique_ x) = let f (unique_ x) = unique_ x in higher_order2 f x
                                                                                   ^
Error: This expression has type unique_ 'a -> 'a
       but an expression was expected of type 'b -> unique_ 'c
|}]

type record_update = { x : int }
[%%expect{|
type record_update = { x : int; }
|}]

let update (unique_ r : record_update) =
  let unique_ x = { unique_ r with x = 1 }
  in x.x
[%%expect{|
val update : unique_ record_update -> int = <fun>
|}]

let update2 = update { x = 3 }
[%%expect{|
val update2 : int = 1
|}]

let inf1 (unique_ x : float) = unique_ let y = x in y
[%%expect{|
val inf1 : unique_ float -> float = <fun>
|}]

let inf2 (b : bool) (unique_ x : float) = unique_ let y = if b then x else 1.0 in y
[%%expect{|
val inf2 : bool -> unique_ float -> float = <fun>
|}]

let inf3 : bool -> float -> unique_ float -> float = fun b y x ->
  let _ = shared_id y in let unique_ z = if b then x else y in z
[%%expect{|
Line 2, characters 58-59:
2 |   let _ = shared_id y in let unique_ z = if b then x else y in z
                                                              ^
Error: Found a shared value where a unique value was expected
|}]

let inf4 (b : bool) (y : float) (unique_ x : float) =
  let _ = shared_id y in let unique_ z = if b then x else y in z
[%%expect{|
Line 2, characters 58-59:
2 |   let _ = shared_id y in let unique_ z = if b then x else y in z
                                                              ^
Error: y is used uniquely here so cannot be used twice. It was used previously at:
Line 2, characters 20-21:
2 |   let _ = shared_id y in let unique_ z = if b then x else y in z
                        ^

|}]


let inf5 (b : bool) (y : float) (unique_ x : float) =
  let z = if b then x else y in unique_ z
[%%expect{|
val inf5 : bool -> unique_ float -> (unique_ float !-> float) = <fun>
|}]

let inf6 (unique_ x) = let f x = x in higher_order f x
[%%expect{|
val inf6 : unique_ 'a -> 'a = <fun>
|}]

let unique_default_args ?(unique_ x = 1.0) () = x
[%%expect{|
val unique_default_args : ?x:unique_ float -> (unit !-> float) = <fun>
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


(* Unique Local *)

let ul (unique_ local_ x) = x
[%%expect{|
val ul : local_ unique_ 'a -> local_ 'a = <fun>
|}]

let ul_ret x = unique_ local_ x
[%%expect{|
val ul_ret : unique_ 'a -> local_ 'a = <fun>
|}]

let or_patterns1 : unique_ float list -> float list !-> float = fun x y -> match x, y with
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
Line 6, characters 14-16:
6 |       unique_ xx
                  ^^
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
val unique_match_on : unique_ 'a -> (unique_ 'b !-> 'a * 'b) = <fun>
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

type point = { x : float; y : float }
[%%expect{|
type point = { x : float; y : float; }
|}]

let overwrite_point t =
  unique_ ({t with y = 0.5}, {t with x = 0.5})
[%%expect{|
val overwrite_point : unique_ point -> point * point = <fun>
|}]

let gc_soundness_bug (local_ unique_ p) (local_ f) =
  local_ { unique_ p with x = f }
[%%expect{|
Line 2, characters 30-31:
2 |   local_ { unique_ p with x = f }
                                  ^
Error: This value escapes its region
|}]

let gc_soundness_nobug (local_ unique_ p) f =
  local_ { unique_ p with x = f }
[%%expect{|
val gc_soundness_nobug :
  local_ unique_ point -> local_ (float !-> local_ point) = <fun>
|}]

let gc_soundness_nobug (local_ unique_ p) (local_ f) =
  local_ { p with x = f }
[%%expect{|
val gc_soundness_nobug :
  local_ unique_ point -> local_ (local_ float !-> local_ point) = <fun>
|}]

let rec foo =
  fun (local_ o) ->
  match (unique_ o) with
  | Some () -> foo None
  | None -> ()
[%%expect{|
val foo : local_ unique_ unit option -> unit = <fun>
|}]

let rec bar =
  fun (unique_ o) ->
  match o with
  | Some () -> ()
  | None -> bar (local_ Some ()) [@nontail]
[%%expect{|
val bar : local_ unique_ unit option -> unit = <fun>
|}]

let foo : local_ unique_ string -> unit = fun (local_ s) -> ()
[%%expect{|
val foo : local_ unique_ string -> unit = <fun>
|}]

let bar : local_ unique_ string -> unit = fun (unique_ s) -> ()
[%%expect{|
val bar : local_ unique_ string -> unit = <fun>
|}]

(* Currying *)

let curry =
  let foo ~a ~b ~c ~d = (a, b, c, (unique_ d)) in
  foo ~a:3 ~c:4
[%%expect{|
val curry : b:'_weak1 -> d:unique_ '_weak2 -> int * '_weak1 * int * '_weak2 =
  <fun>
|}]

let curry =
  let foo ~a ~b ~c ~d = (a, b, (unique_ c), (unique_ d)) in
  foo ~a:3 ~c:4
[%%expect{|
val curry : b:'_weak3 !-> d:unique_ '_weak4 !-> int * '_weak3 * int * '_weak4 =
  <fun>
|}]

let curry =
  let foo ~a ~b ~c ~d = ((unique_ a), b, c, d) in
  foo ~a:3 ~c:4
[%%expect{|
val curry : b:'_weak5 !-> d:'_weak6 !-> int * '_weak5 * int * '_weak6 = <fun>
|}]

let curry =
  let foo ~a ~b ~c ~d = (a, (unique_ b), c, unique_ d) in
  foo ~a:3 ~c:4
[%%expect{|
val curry :
  b:unique_ '_weak7 -> (d:unique_ '_weak8 !-> int * '_weak7 * int * '_weak8) =
  <fun>
|}]

let curry =
  let foo ~a ~b ~c ~d = (a, b, (unique_ c), unique_ d) in
  let bar = foo ~a:3 ~b:2 ~c:4 in
  (bar ~d:3, bar ~d:5)
[%%expect{|
Line 4, characters 13-16:
4 |   (bar ~d:3, bar ~d:5)
                 ^^^
Error: bar is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 3-6:
4 |   (bar ~d:3, bar ~d:5)
       ^^^

|}]

let curry =
  let foo ~a ~b ~c ~d = (a, b, (unique_ c), unique_ d) in
  let bar = foo ~a:3 ~c:4 in
  let baz = bar ~b:4 in (baz ~d:3, baz ~d:5)
[%%expect{|
Line 4, characters 35-38:
4 |   let baz = bar ~b:4 in (baz ~d:3, baz ~d:5)
                                       ^^^
Error: baz is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 25-28:
4 |   let baz = bar ~b:4 in (baz ~d:3, baz ~d:5)
                             ^^^

|}]

let curry =
  let unique_ x = 3 in
  let foo y = unique_ x in
  (foo 1, foo 2)
[%%expect{|
Line 4, characters 10-13:
4 |   (foo 1, foo 2)
              ^^^
Error: foo is used uniquely here so cannot be used twice. It will be used again at:
Line 4, characters 3-6:
4 |   (foo 1, foo 2)
       ^^^

|}]

let unique_ x = [1;2;3]
[%%expect{|
Line 1, characters 12-13:
1 | let unique_ x = [1;2;3]
                ^
Error: Unique values are not supported at toplevel.
|}]

let x = [1;2;3]
[%%expect{|
val x : int list = [1; 2; 3]
|}]

let toplevel y = unique_ x
[%%expect{|
Line 1, characters 25-26:
1 | let toplevel y = unique_ x
                             ^
Error: Found a shared value where a unique value was expected
  Hint: This identifier was defined outside of the current closure.
  Did you forget to use a !-> arrow in a function type?
|}]

(* Borrowing *)

let borrow_overwritten_by_once p (unique_ x) =
  let _x = if p then (borrow_ x) else unique_id x in local_ (Some 5)
[%%expect{|
val foo : bool -> unique_ 'a -> local_ int option = <fun>
|}]

(* ------------------------------------------------------------------------------------ *)
(* Tests for locals, adapted to uniqueness *)
(* ------------------------------------------------------------------------------------ *)

(* If both type and mode are wrong, complain about type *)
let f () =
  let id2 (x : string) = shared_id x in
  let unique_ r = 42 in
  id2 r
[%%expect{|
Line 4, characters 6-7:
4 |   id2 r
          ^
Error: This expression has type int but an expression was expected of type
         string
|}]

(*
 * Type equalities of function types
*)

(* When a [unique_] argument appears in a function type with multiple arguments,
   return modes are implicitly FnOnce until the final argument. *)
type equ_fn = unit
  constraint
    'a -> unique_ 'b -> 'c -> 'd -> 'e
    = 'a -> unique_ 'b -> unique_ ('c !-> unique_ ('d !-> 'e)) (* TODO: Add !-> *)
[%%expect{|
type equ_fn = unit
|}]

type distinct_sarg = unit constraint unique_ int -> int = int -> int
[%%expect{|
Line 1, characters 37-68:
1 | type distinct_sarg = unit constraint unique_ int -> int = int -> int
                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type unique_ int -> int is not compatible with type int -> int
|}]
type distinct_sret = unit constraint int -> unique_ int = int -> int
[%%expect{|
Line 1, characters 37-68:
1 | type distinct_sret = unit constraint int -> unique_ int = int -> int
                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type int -> unique_ int is not compatible with type int -> int
|}]
type distinct_sarg_sret = unit constraint unique_ int -> int = unique_ int -> unique_ int
[%%expect{|
Line 1, characters 42-89:
1 | type distinct_sarg_sret = unit constraint unique_ int -> int = unique_ int -> unique_ int
                                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type unique_ int -> int is not compatible with type
  unique_ int -> unique_ int
|}]

let foo () =
  let unique_ _bar : int -> int -> int =
    ((fun y z -> z) : int -> unique_ (int -> int)) in
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]
