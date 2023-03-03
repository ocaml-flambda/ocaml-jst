(* TEST
   flags = "-extension comprehensions_experimental -extension immutable_arrays_experimental"
   * expect
*)

(******************************************************************************
 *                        ******** ATTENTION! ********                        *
 *                                                                            *
 * This file should be kept in sync with the files                            *
 * "list_comprehensions_pure.ml" and "iarray_comprehensions_pure.ml".  If     *
 * you're adding a test to one, add it to the others as well; if the test     *
 * output changes in one file and not the others (except as documented in     *
 * comments), this is a bug.                                                  *
 ******************************************************************************)

(******************************************************************************)
(**** Basic behavior ****)

[:i for i = 0 to 9:];;
[%%expect{|
- : int iarray = [:0; 1; 2; 3; 4; 5; 6; 7; 8; 9:]
|}];;

[:i for i = 9 downto 0:];;
[%%expect{|
- : int iarray = [:9; 8; 7; 6; 5; 4; 3; 2; 1; 0:]
|}];;

[:s for s in [:"hello"; "world"; "!":]:];;
[%%expect{|
- : string iarray = [:"hello"; "world"; "!":]
|}];;

[:i,s for i = 0 to 3 and s in [:'a'; 'b'; 'c':]:];;
[%%expect{|
- : (int * char) iarray =
[:(0, 'a'); (0, 'b'); (0, 'c'); (1, 'a'); (1, 'b'); (1, 'c'); (2, 'a');
  (2, 'b'); (2, 'c'); (3, 'a'); (3, 'b'); (3, 'c'):]
|}];;

[:i,s for i = 0 to 3 for s in [:'a'; 'b'; 'c':]:];;
[%%expect{|
- : (int * char) iarray =
[:(0, 'a'); (0, 'b'); (0, 'c'); (1, 'a'); (1, 'b'); (1, 'c'); (2, 'a');
  (2, 'b'); (2, 'c'); (3, 'a'); (3, 'b'); (3, 'c'):]
|}];;

[:i,j for i = 1 to 3 for j in [:i*10; i*100:]:];;
[%%expect{|
- : (int * int) iarray =
[:(1, 10); (1, 100); (2, 20); (2, 200); (3, 30); (3, 300):]
|}];;

[:x for xs in [:[:"this"; "is"; "one":];
                [:"way":];
                [:"to"; "flatten":];
                [:"a"; "nested"; "array":]:]
    for x in xs:];;
[%%expect{|
- : string iarray =
[:"this"; "is"; "one"; "way"; "to"; "flatten"; "a"; "nested"; "array":]
|}];;

[:i for i = 0 to 10 when i mod 2 = 0:];;
[%%expect{|
- : int iarray = [:0; 2; 4; 6; 8; 10:]
|}];;

[:() for _ = 1 to 10:];;
[%%expect{|
- : unit iarray = [:(); (); (); (); (); (); (); (); (); ():]
|}];;

(******************************************************************************)
(**** More complex behavior ****)

let pythagorean_triples n =
  [:a,b,c for a = 1 to n for b = a to n for c = b to n when a*a + b*b = c*c:]
in
pythagorean_triples 10;;
[%%expect{|
- : (int * int * int) iarray = [:(3, 4, 5); (6, 8, 10):]
|}];;

let tails xs =
  let len = Iarray.length xs in
  Iarray.init (len + 1) (fun i -> Iarray.sub xs i (len - i))
in
let sum = Iarray.fold_left ( + ) 0 in
[:sum xs for xs in tails [:1; 20; 300; 4_000; 50_000; 600_000; 7_000_000:]:];;
[%%expect{|
- : int iarray =
[:7654321; 7654320; 7654300; 7654000; 7650000; 7600000; 7000000; 0:]
|}];;

let xs = [:2;7;18;28:] in
[:x + 1000*y for x in xs and y in xs:];;
[%%expect{|
- : int iarray =
[:2002; 7002; 18002; 28002; 2007; 7007; 18007; 28007; 2018; 7018; 18018;
  28018; 2028; 7028; 18028; 28028:]
|}];;

(******************************************************************************)
(**** Edge cases ****)

[:42 when true:];;
[%%expect{|
- : int iarray = [:42:]
|}];;

[:42 when false:];;
[%%expect{|
- : int iarray = [::]
|}];;

[:x for x in [::]:];;
[%%expect{|
- : 'a iarray = [::]
|}];;

[:i for i = 0 to -1:];;
[%%expect{|
- : int iarray = [::]
|}];;

[:i for i = 0 downto 1:];;
[%%expect{|
- : int iarray = [::]
|}];;

[:i for i = 0 to 0:];;
[%%expect{|
- : int iarray = [:0:]
|}];;

[:i for i = 0 downto 0:];;
[%%expect{|
- : int iarray = [:0:]
|}];;

(* This would take ~forever if the empty array were iterated over later;
   however, for arrays, using [and] lets us get more flexibility (see below). *)
[:i,j,k for i in [::] for j = 0 to Int.max_int for k = 0 downto Int.min_int:];;
[%%expect{|
- : ('a * int * int) iarray = [::]
|}];;

(* This works no matter where the empty array is, but would take ~forever for
   lists if the empty list were iterated over later; see
   "(i)array_comprehensions_special.ml" for more nuance on what can happen here
   with arrays. *)
[:i,j,k for i in [::] and j = 0 to Int.max_int and k = 0 downto Int.min_int:];;
[%%expect{|
- : ('a * int * int) iarray = [::]
|}];;

[:x for x in [:"one"; "two"; "three":] for x in [:10; 20; 30:]:];;
[%%expect{|
Line 1, characters 8-9:
1 | [:x for x in [:"one"; "two"; "three":] for x in [:10; 20; 30:]:];;
            ^
Warning 26 [unused-var]: unused variable x.
- : int iarray = [:10; 20; 30; 10; 20; 30; 10; 20; 30:]
|}];;

(******************************************************************************)
(**** Variable shadowing ****)

(* QuickCheck found that Python doesn't shadow variables in list comprehensions;
   instead, using the same variable name as the binder in two `for`-clauses
   doesn't shadow, but rather overwrites the same mutable cell.  To confirm that
   we handle the subtle issue of shadowing correctly, we preserve here the cases
   that Python does not, as found by QuickCheck. *)

(* Python: {v
     [a for a in [0] for a in [1]] == [1]
   v} *)
[:a for a in [:0:] for a in [:1:]:];;
[%%expect{|
Line 1, characters 8-9:
1 | [:a for a in [:0:] for a in [:1:]:];;
            ^
Warning 26 [unused-var]: unused variable a.
- : int iarray = [:1:]
|}];;

(* Python: {v
     [(a, b)
        for b in [0]
        for _ in [0, 0]
        for a in [b]
        for b in range(0, -2, -1)]
     == [(0, 0), (0, -1), (-1, 0), (-1, -1)]
   v} *)
[:(a, b) for b in [:0:] for _ in [:0; 0:] for a in [:b:] and b = 0 downto -1:];;
[%%expect{|
- : (int * int) iarray = [:(0, 0); (0, -1); (0, 0); (0, -1):]
|}];;

(* Python: {v
     [(a, b) for b in [1] for b in [0] for a in [b]] == [(0, 0)]
   v} *)
[:(a, b) for b in [:1:] for b in [:0:] and a in [:b:]:];;
[%%expect{|
- : (int * int) iarray = [:(1, 0):]
|}];;

(* Python: {v
     [a for a in [1] for _ in [0, 0] if a > 0 for a in [0]] == [0]
   v} *)
[:a for a in [:1:] and _ in [:0; 0:] when a > 0 for a in [:0:]:];;
[%%expect{|
- : int iarray = [:0; 0:]
|}];;

(* Python: {v
     [a for a in [0] for _ in [0, 0] for a in [a, 1]] == [0, 1, 1, 1]
   v} *)
[:a for a in [:0:] and _ in [:0; 0:] for a in [:a; 1:]:];;
[%%expect{|
- : int iarray = [:0; 1; 0; 1:]
|}];;

(******************************************************************************)
(**** Bugs found by QuickCheck ****)

(* At one time, this was (for mutable arrays) incorrectly returning the empty
   array as an array comprehension, but correctly returning a singleton list as
   a list comprehension. *)
[:() for _ = 0 to 0:];
[%%expect{|
- : unit iarray = [:():]
|}];;

(******************************************************************************)
(**** Errors ****)

(* Can't iterate over non-arrays *)

[:x for x in 100:];;
[%%expect{|
Line 1, characters 13-16:
1 | [:x for x in 100:];;
                 ^^^
Error: This expression has type int but an expression was expected of type
         'a iarray
       because it is in a for-in iterator in an immutable array comprehension
|}];;

(* No mixing immutable arrays and either lists or mutable arrays *)

(* It's unclear why these are different based on principality *)
[:x for x in []:];;
[%%expect{|
Line 1, characters 13-15:
1 | [:x for x in []:];;
                 ^^
Error: This expression has type 'a list
       but an expression was expected of type 'b iarray
|}, Principal{|
Line 1, characters 13-15:
1 | [:x for x in []:];;
                 ^^
Error: This expression has type 'a list
       but an expression was expected of type 'b iarray
       because it is in a for-in iterator in an immutable array comprehension
|}];;

(* As above, but don't trigger type-based disambiguation; this affects the error
   message for array comprehensions, but is invisible for list comprehensions *)
let empty = [] in
[:x for x in empty:];;
[%%expect{|
Line 2, characters 13-18:
2 | [:x for x in empty:];;
                 ^^^^^
Error: This expression has type 'a list
       but an expression was expected of type 'b iarray
       because it is in a for-in iterator in an immutable array comprehension
|}];;

List.length [:i for i = 0 to 3:];;
[%%expect{|
Line 1, characters 12-32:
1 | List.length [:i for i = 0 to 3:];;
                ^^^^^^^^^^^^^^^^^^^^
Error: This expression has type 'a iarray
       but an expression was expected of type 'b list
|}];;

[:x for x in [||]:];;
[%%expect{|
Line 1, characters 13-17:
1 | [:x for x in [||]:];;
                 ^^^^
Error: This expression has type 'a array
       but an expression was expected of type 'b iarray
       because it is in a for-in iterator in an immutable array comprehension
|}];;

let empty = [||] in
[:x for x in empty:];;
[%%expect{|
Line 2, characters 13-18:
2 | [:x for x in empty:];;
                 ^^^^^
Error: This expression has type 'a array
       but an expression was expected of type 'b iarray
       because it is in a for-in iterator in an immutable array comprehension
|}];;

Array.length [:i for i = 0 to 3:];;
[%%expect{|
Line 1, characters 13-33:
1 | Array.length [:i for i = 0 to 3:];;
                 ^^^^^^^^^^^^^^^^^^^^
Error: This expression has type 'a iarray
       but an expression was expected of type 'b array
|}];;

(* No mixing immutable arrays with anything else; we check these here so we
   don't have to enable -extension immutable_arrays elsewhere, but we should
   move them when that changes *)

[x for x in [::]];;
[%%expect{|
Line 1, characters 12-16:
1 | [x for x in [::]];;
                ^^^^
Error: This expression has type 'a iarray
       but an expression was expected of type 'b list
       because it is in a for-in iterator in a list comprehension
|}];;

(* As above, but don't trigger type-based disambiguation; this is invisible for
   list comprehensions but affects the error message for array comprehensions *)
let empty = [::] in
[x for x in empty];;
[%%expect{|
Line 2, characters 12-17:
2 | [x for x in empty];;
                ^^^^^
Error: This expression has type 'a iarray
       but an expression was expected of type 'b list
       because it is in a for-in iterator in a list comprehension
|}];;

Iarray.length [i for i = 0 to 3];;
[%%expect{|
Line 1, characters 14-32:
1 | Iarray.length [i for i = 0 to 3];;
                  ^^^^^^^^^^^^^^^^^^
Error: This expression has type 'a list
       but an expression was expected of type 'b iarray
|}];;

[|x for x in [::]|];;
[%%expect{|
Line 1, characters 13-17:
1 | [|x for x in [::]|];;
                 ^^^^
Error: This expression has type 'a iarray
       but an expression was expected of type 'b array
       because it is in a for-in iterator in an array comprehension
|}];;

(* As above, but don't trigger type-based disambiguation; this is invisible for
   list comprehensions but affects the error message for array comprehensions *)
let empty = [::] in
[|x for x in empty|];;
[%%expect{|
Line 2, characters 13-18:
2 | [|x for x in empty|];;
                 ^^^^^
Error: This expression has type 'a iarray
       but an expression was expected of type 'b array
       because it is in a for-in iterator in an array comprehension
|}];;

Iarray.length [i for i = 0 to 3];;
[%%expect{|
Line 1, characters 14-32:
1 | Iarray.length [i for i = 0 to 3];;
                  ^^^^^^^^^^^^^^^^^^
Error: This expression has type 'a list
       but an expression was expected of type 'b iarray
|}];;

(* to/downto are only for ints *)

[:x for x = 1.5 to 4.2:];;
[%%expect{|
Line 1, characters 12-15:
1 | [:x for x = 1.5 to 4.2:];;
                ^^^
Error: This expression has type float but an expression was expected of type
         int
       because it is in a range-based for iterator start index in a comprehension
|}];;

[:x for x = 4.2 downto 1.5:];;
[%%expect{|
Line 1, characters 12-15:
1 | [:x for x = 4.2 downto 1.5:];;
                ^^^
Error: This expression has type float but an expression was expected of type
         int
       because it is in a range-based for iterator start index in a comprehension
|}];;

(* Using first-class module patterns isn't supported yet *)

module type S = sig
  type t
  val x : t
end;;

let t = (module struct
  type t = int
  let x = 3
end : S);;
[%%expect {|
module type S = sig type t val x : t end
val t : (module S) = <module>
|}];;

let f () =
  [: M.x for (module M : S) in [: t :] :];;
[%%expect {|
Line 2, characters 21-22:
2 |   [: M.x for (module M : S) in [: t :] :];;
                         ^
Error: Modules are not allowed in this pattern.
|}];;

let f () =
  [: M.x
    for (module M :S) in
    [: (module struct
         type t = int
         let x = 3
        end : S)
    :]
  :];;
[%%expect {|
Line 3, characters 16-17:
3 |     for (module M :S) in
                    ^
Error: Modules are not allowed in this pattern.
|}];;

let f () =
  [: M.x
    for (module M :S) in
    [: (let t = t in
        t)
    :]
  :];;
[%%expect {|
Line 3, characters 16-17:
3 |     for (module M :S) in
                    ^
Error: Modules are not allowed in this pattern.
|}];;

(* No duplicating variables in a for-and clause *)

[:i for i = 1 to 3 and i = 3 downto 1:];;
[%%expect{|
Line 1, characters 0-39:
1 | [:i for i = 1 to 3 and i = 3 downto 1:];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Variable i is bound several times in this matching
|}];;

(* Variables bind from left to right, not right to left *)

[:outer,inner for outer = inner to 3 for inner = 1 to 3:];;
[%%expect{|
Line 1, characters 26-31:
1 | [:outer,inner for outer = inner to 3 for inner = 1 to 3:];;
                              ^^^^^
Error: Unbound value inner
Hint: Did you mean incr?
|}];;

(* The element type is handled correctly *)

Iarray.append [:true:] [:i for i = 0 to 10:];;
[%%expect{|
Line 1, characters 25-26:
1 | Iarray.append [:true:] [:i for i = 0 to 10:];;
                             ^
Error: This expression has type int but an expression was expected of type
         bool
|}];;

(******************************************************************************)
(**** Test that types are being propagated inwards correctly ****)

(* Prepare a module for later use *)
module M = struct
  type t = A | B
end;;
[%%expect{|
module M : sig type t = A | B end
|}];;

let x : M.t iarray  = [:A for _ = 1 to 3:];;
[%%expect{|
val x : M.t iarray = [:M.A; M.A; M.A:]
|}];;

[:A for _ = 1 to 3:];;
[%%expect{|
Line 1, characters 2-3:
1 | [:A for _ = 1 to 3:];;
      ^
Error: Unbound constructor A
|}];;

Iarray.append [:M.B:] [:A for _ = 1 to 3:];;
[%%expect{|
- : M.t iarray = [:M.B; M.A; M.A; M.A:]
|}, Principal{|
Line 1, characters 24-25:
1 | Iarray.append [:M.B:] [:A for _ = 1 to 3:];;
                            ^
Warning 18 [not-principal]: this type-based constructor disambiguation is not principal.
- : M.t iarray = [:M.B; M.A; M.A; M.A:]
|}];;
