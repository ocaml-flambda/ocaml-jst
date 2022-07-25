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

let dup x = unique_ (x, x)
[%%expect{|
Line 1, characters 24-25:
1 | let dup x = unique_ (x, x)
                            ^
Error: The identifier x was inferred to be unique and thus can not
       be used twice.
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
Error: The identifier x was inferred to be unique and thus can not
       be used twice. It was seen here because y is a parent or alias of x.
|}]

let children_unique (unique_ xs : float list) = unique_ match xs with
  | [] -> (0., [])
  | x :: xx -> (x, xx)
[%%expect{|
val children_unique : unique_ float list -> float * float list = <fun>
|}]

let borrow_match (unique_ fs : 'a list) = unique_ match fs with
  | [] -> []
  | x :: xs as gs -> gs
[%%expect{|
val borrow_match : unique_ 'a list -> 'a list = <fun>
|}]

let dup_child (unique_ fs : 'a list) = unique_ match fs with
  | [] -> ([], [])
  | x :: xs as gs -> (gs, xs)
[%%expect{|
Line 3, characters 26-28:
3 |   | x :: xs as gs -> (gs, xs)
                              ^^
Error: The identifier xs was inferred to be unique and thus can not
       be used twice. It was seen previously because gs is a parent or alias of xs.
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

let update (unique_ r : record_update) = unique_ { unique_ r with x = 1 }
[%%expect{|
val update : unique_ record_update -> record_update = <fun>
|}]

let inf1 (unique_ x : float) = unique_ let y = x in y
[%%expect{|
val inf1 : unique_ float -> float = <fun>
|}]

let inf2 (b : bool) (unique_ x : float) = unique_ let y = if b then x else 1.0 in y
[%%expect{|
val inf2 : bool -> unique_ float -> float = <fun>
|}]

let inf3 (b : bool) (y : float) (unique_ x : float) = unique_ let z = if b then x else y in z
[%%expect{|
Line 1, characters 87-88:
1 | let inf3 (b : bool) (y : float) (unique_ x : float) = unique_ let z = if b then x else y in z
                                                                                           ^
Error: The identifier y was inferred to be unique and thus can not be
       used in a context where unique use is not guaranteed.
|}]
(* [%%expect{|
 *   Error: z is not unique
 * |}] *)

let inf4 (unique_ x) = let f x = x in unique_ higher_order f x
[%%expect{|
val inf4 : unique_ 'a -> 'a = <fun>
|}]

let unique_default_args ?(unique_ x = 1.0) () = x
[%%expect{|
val unique_default_args : ?x:unique_ float -> unit -> float = <fun>
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

(* ------------------------------------------------------------------------------------ *)
(* Tests for locals, adapted to uniqueness *)
(* ------------------------------------------------------------------------------------ *)

let leak n =
  let unique_ r : int ref = ref n in
  r
[%%expect{|
val leak : int -> int ref = <fun>
|}]

let leak n =
  let unique_ f : 'a. 'a -> 'a = fun x -> x in
  f
[%%expect{|
val leak : 'a -> 'b -> 'b = <fun>
|}]

(* If both type and mode are wrong, complain about type *)
let f () =
  let id2 (unique_ x : string) = x in
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
    = 'a -> unique_ 'b -> unique_ ('c -> unique_ ('d -> 'e)) (* TODO: Add !-> *)
[%%expect{|
Lines 3-4, characters 4-60:
3 | ....'a -> unique_ 'b -> 'c -> 'd -> 'e
4 |     = 'a -> unique_ 'b -> unique_ ('c -> unique_ ('d -> 'e))....................
Error: The type constraints are not consistent.
Type 'a -> unique_ 'b -> ('c -> 'd -> 'e) is not compatible with type
  'a -> unique_ (unique_ 'b -> 'c -> 'd -> 'e)
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

type unique_higher_order = unit constraint
  unique_ (int -> int -> int) -> int = unique_ (int -> unique_ (int -> int)) -> int
[%%expect{|
Line 2, characters 2-83:
2 |   unique_ (int -> int -> int) -> int = unique_ (int -> unique_ (int -> int)) -> int
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type unique_ (int -> (int -> int)) -> int is not compatible with type
  unique_ (int -> int -> int) -> int
Type int -> int -> int is not compatible with type
  int -> unique_ (int -> int)
|}]

type nonunique_higher_order = unit constraint
  (int -> int -> int) -> int = (int -> unique_ (int -> int)) -> int
[%%expect{|
Line 2, characters 2-67:
2 |   (int -> int -> int) -> int = (int -> unique_ (int -> int)) -> int
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type (int -> int -> int) -> int is not compatible with type
  (int -> unique_ (int -> int)) -> int
Type int -> int -> int is not compatible with type
  int -> unique_ (int -> int)
|}]

type unique_higher_order = unit constraint
  int -> unique_ (int -> int -> int) = int -> unique_ (int -> unique_ (int -> int))
[%%expect{|
Line 2, characters 2-83:
2 |   int -> unique_ (int -> int -> int) = int -> unique_ (int -> unique_ (int -> int))
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type int -> unique_ (int -> (int -> int)) is not compatible with type
  int -> unique_ (int -> int -> int)
Type int -> int -> int is not compatible with type
  int -> unique_ (int -> int)
|}]

type nonunique_higher_order = unit constraint
  int -> (int -> int -> int) = int -> (int -> unique_ (int -> int))
[%%expect{|
Line 2, characters 2-67:
2 |   int -> (int -> int -> int) = int -> (int -> unique_ (int -> int))
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
Type int -> int -> int -> int is not compatible with type
  int -> int -> unique_ (int -> int)
Type int -> int -> int is not compatible with type
  int -> unique_ (int -> int)
|}]

let foo () =
  let unique_ _bar : int -> int -> int =
    ((fun y z -> z) : int -> unique_ (int -> int)) in (* TODO: is that correct? *)
  ()
[%%expect{|
Line 3, characters 5-19:
3 |     ((fun y z -> z) : int -> unique_ (int -> int)) in (* TODO: is that correct? *)
         ^^^^^^^^^^^^^^
Error: This function or one of its parameters escape their region
       when it is partially applied
|}]
