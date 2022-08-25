(* TEST
  flags = "-extension Comprehensions"
   * expect
*)

(******************************************************************************
 *                        ******** ATTENTION! ********                        *
 *                                                                            *
 * This file should be kept in sync with the file                             *
 * "array_comprehensions_pure.ml".  If you're adding a test to one, add it to *
 * the other as well; if the test output changes in one file and not the      *
 * other (except as documented in comments), this is a bug.                   *
 ******************************************************************************)

(******************************************************************************)
(**** Basic behavior ****)

[i for i = 0 to 9];;
[%%expect{|
- : int list = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]
|}];;

[i for i = 9 downto 0];;
[%%expect{|
- : int list = [9; 8; 7; 6; 5; 4; 3; 2; 1; 0]
|}];;

[s for s in ["hello"; "world"; "!"]];;
[%%expect{|
- : string list = ["hello"; "world"; "!"]
|}];;

[i,s for i = 0 to 3 and s in ['a'; 'b'; 'c']];;
[%%expect{|
- : (int * char) list =
[(0, 'a'); (0, 'b'); (0, 'c'); (1, 'a'); (1, 'b'); (1, 'c'); (2, 'a');
 (2, 'b'); (2, 'c'); (3, 'a'); (3, 'b'); (3, 'c')]
|}];;

[i,s for i = 0 to 3 for s in ['a'; 'b'; 'c']];;
[%%expect{|
- : (int * char) list =
[(0, 'a'); (1, 'a'); (2, 'a'); (3, 'a'); (0, 'b'); (1, 'b'); (2, 'b');
 (3, 'b'); (0, 'c'); (1, 'c'); (2, 'c'); (3, 'c')]
|}];;

[i,j for j in [i*10; i*100] for i = 1 to 3];;
[%%expect{|
- : (int * int) list =
[(1, 10); (1, 100); (2, 20); (2, 200); (3, 30); (3, 300)]
|}];;

[x for x in xs
   for xs in [["this"; "is"; "one"];
              ["way"];
              ["to"; "flatten"];
              ["a"; "nested"; "list"]]];;
[%%expect{|
- : string list =
["this"; "is"; "one"; "way"; "to"; "flatten"; "a"; "nested"; "list"]
|}];;

[i when i mod 2 = 0 for i = 0 to 10];;
[%%expect{|
- : int list = [0; 2; 4; 6; 8; 10]
|}];;

[() for _ = 1 to 10];;
[%%expect{|
- : unit list = [(); (); (); (); (); (); (); (); (); ()]
|}];;

(******************************************************************************)
(**** More complex behavior ****)

let pythagorean_triples n =
  [a,b,c when a*a + b*b = c*c for c = b to n for b = a to n for a = 1 to n]
in
pythagorean_triples 10;;
[%%expect{|
- : (int * int * int) list = [(3, 4, 5); (6, 8, 10)]
|}];;

let tails xs =
  List.fold_right (fun hd tls -> (hd :: List.hd tls) :: tls) xs [[]]
in
let sum = List.fold_left ( + ) 0 in
[sum xs for xs in tails [1; 20; 300; 4_000; 50_000; 600_000; 7_000_000]];;
[%%expect{|
- : int list =
[7654321; 7654320; 7654300; 7654000; 7650000; 7600000; 7000000; 0]
|}];;

let xs = [2;7;18;28] in
[x + 1000*y for x in xs and y in xs];;
[%%expect{|
- : int list =
[2002; 7002; 18002; 28002; 2007; 7007; 18007; 28007; 2018; 7018; 18018;
 28018; 2028; 7028; 18028; 28028]
|}];;

(******************************************************************************)
(**** Edge cases ****)

[42 when true];;
[%%expect{|
- : int list = [42]
|}];;

[42 when false];;
[%%expect{|
- : int list = []
|}];;

[x for x in []];;
[%%expect{|
- : 'a list = []
|}];;

[i for i = 0 to -1];;
[%%expect{|
- : int list = []
|}];;

[i for i = 0 downto 1];;
[%%expect{|
- : int list = []
|}];;

[i for i = 0 to 0];;
[%%expect{|
- : int list = [0]
|}];;

[i for i = 0 downto 0];;
[%%expect{|
- : int list = [0]
|}];;

(* This is expected to succeed for lists and fail for arrays (although it would
   take ~forever for lists if the empty list were iterated over later); see
   "array_comprehensions_special.ml" for more nuance on what can happen here
   with arrays. *)
[i,j,k for i in [] and j = 0 to Int.max_int and k = 0 downto Int.min_int];;
[%%expect{|
- : ('a * int * int) list = []
|}];;

[x for x in ["one"; "two"; "three"] for x in [10; 20; 30]];;
[%%expect{|
Line 1, characters 40-41:
1 | [x for x in ["one"; "two"; "three"] for x in [10; 20; 30]];;
                                            ^
Warning 26 [unused-var]: unused variable x.
- : string list =
["one"; "two"; "three"; "one"; "two"; "three"; "one"; "two"; "three"]
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
[a for a in [0] and a in [1]];;
[%%expect{|
Line 1, characters 20-21:
1 | [a for a in [0] and a in [1]];;
                        ^
Error: The variable a is bound several times in this comprehension's for-and binding
|}];;

(* Python: {v
     [a for a in [0] for a in [1]] == [1]
   v} *)
[a for a in [1] for a in [0]];;
[%%expect{|
Line 1, characters 20-21:
1 | [a for a in [1] for a in [0]];;
                        ^
Warning 26 [unused-var]: unused variable a.
- : int list = [1]
|}];;

(* Python: {v
     [(a, b)
        for b in [0]
        for _ in [0, 0]
        for a in [b]
        for b in range(0, -2, -1)]
     == [(0, 0), (0, -1), (-1, 0), (-1, -1)]
   v} *)
[(a, b) for a in [b] and b = 0 downto -1 for _ in [0; 0] for b in [0]];;
[%%expect{|
- : (int * int) list = [(0, 0); (0, -1); (0, 0); (0, -1)]
|}];;

(* Python: {v
     [(a, b) for b in [1] for b in [0] for a in []b]] == [(0, 0)
   v} *)
[(a, b) for b in [0] and a in [b] for b in [1]];;
[%%expect{|
- : (int * int) list = [(1, 0)]
|}];;

(* Python: {v
     [a for a in [1] for _ in [0, 0] if a > 0 for a in [0]] == [0]
   v} *)
[a for a in [0] when a > 0 for a in [1] and _ in [0; 0]];;
[%%expect{|
- : int list = [0; 0]
|}];;

(* Python: {v
     [a for a in [0] for _ in [0, 0] for a in [a, 1]] == [0, 1, 1, 1]
   v} *)
[a for a in [a; 1] for a in [0] and _ in [0; 0]];;
[%%expect{|
- : int list = [0; 1; 0; 1]
|}];;

(******************************************************************************)
(**** Bugs found by QuickCheck ****)

(* At one time, this was correctly returning a singleton list as a list
 * comprehension, but incorrectly returning the empty array as an array
 * comprehension. *)
[() for _ = 0 to 0];
[%%expect{|
- : unit list = [()]
|}];;

(******************************************************************************)
(**** Errors ****)

(* Can't iterate over non-lists *)

[x for x in 100];;
[%%expect{|
Line 1, characters 12-15:
1 | [x for x in 100];;
                ^^^
Error: This expression has type int but an expression was expected of type
         'a list
       because it is in a for-in iterator in a list comprehension
|}];;

(* No mixing lists and arrays *)

[x for x in [||]];;
[%%expect{|
Line 1, characters 12-16:
1 | [x for x in [||]];;
                ^^^^
Error: This expression has type 'a array
       but an expression was expected of type 'b list
       because it is in a for-in iterator in a list comprehension
|}];;

Array.length [i for i = 0 to 3];;
[%%expect{|
Line 1, characters 13-31:
1 | Array.length [i for i = 0 to 3];;
                 ^^^^^^^^^^^^^^^^^^
Error: This expression has type 'a list
       but an expression was expected of type 'b array
|}];;

(* to/downto are only for ints *)

[x for x = 1.5 to 4.2];;
[%%expect{|
Line 1, characters 11-14:
1 | [x for x = 1.5 to 4.2];;
               ^^^
Error: This expression has type float but an expression was expected of type
         int
       because it is in a range-based for iterator start index in a comprehension
|}];;

[x for x = 4.2 downto 1.5];;
[%%expect{|
Line 1, characters 11-14:
1 | [x for x = 4.2 downto 1.5];;
               ^^^
Error: This expression has type float but an expression was expected of type
         int
       because it is in a range-based for iterator start index in a comprehension
|}];;

(* No duplicating variables in a for-and clause *)

[i for i = 1 to 3 and i = 3 downto 1];;
[%%expect{|
Line 1, characters 0-37:
1 | [i for i = 1 to 3 and i = 3 downto 1];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The variable i is bound several times in this comprehension's for-and binding
|}];;

(* The element type is handled correctly *)

true :: [i for i = 0 to 10];;
[%%expect{|
Line 1, characters 9-10:
1 | true :: [i for i = 0 to 10];;
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

let x : M.t list  = [A for _ = 1 to 3];;
[%%expect{|
val x : M.t list = [M.A; M.A; M.A]
|}];;

[A for _ = 1 to 3];;
[%%expect{|
Line 1, characters 1-2:
1 | [A for _ = 1 to 3];;
     ^
Error: Unbound constructor A
|}];;

M.B :: [A for _ = 1 to 3];;
[%%expect{|
- : M.t list = [M.B; M.A; M.A; M.A]
|}, Principal{|
Line 1, characters 8-9:
1 | M.B :: [A for _ = 1 to 3];;
            ^
Warning 18 [not-principal]: this type-based constructor disambiguation is not principal.
- : M.t list = [M.B; M.A; M.A; M.A]
|}];;