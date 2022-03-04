(* TEST
  flags = "-extension Comprehensions"
   * expect
*)
(*Type checking tests.*)
true::[i for i = 10 downto 0];;
[%%expect{|
Line 1, characters 7-8:
1 | true::[i for i = 10 downto 0];;
           ^
Error: This expression has type int but an expression was expected of type
         bool
|}];;

module M = struct type t = A | B end;;
let x : M.t list  = [A for i = 1 to 1];;
[%%expect{|
module M : sig type t = A | B end
Line 2, characters 20-38:
2 | let x : M.t list  = [A for i = 1 to 1];;
                        ^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
val x : M.t list = [M.A]
|}];;

[A for i = 1 to 1];;
[%%expect{|
Line 1, characters 1-2:
1 | [A for i = 1 to 1];;
     ^
Error: Unbound constructor A
|}];;

M.B::[A for i = 1 to 1];;
[%%expect{|
Line 1, characters 5-23:
1 | M.B::[A for i = 1 to 1];;
         ^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : M.t list = [M.B; M.A]
|}, Principal{|
Line 1, characters 6-7:
1 | M.B::[A for i = 1 to 1];;
          ^
Warning 18 [not-principal]: this type-based constructor disambiguation is not principal.
Line 1, characters 5-23:
1 | M.B::[A for i = 1 to 1];;
         ^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : M.t list = [M.B; M.A]
|}];;

let y = 10;;
[i for i in y];;
[%%expect{|
val y : int = 10
Line 2, characters 12-13:
2 | [i for i in y];;
                ^
Error: This expression has type int but an expression was expected of type
         'a list
       because it is in a for-in iterator in a comprehension
|}];;

let y = [1;2;3];;
true::[i for i in y];;
[%%expect{|
val y : int list = [1; 2; 3]
Line 2, characters 7-8:
2 | true::[i for i in y];;
           ^
Error: This expression has type int but an expression was expected of type
         bool
|}];;

let y = [[1]];;
true::[i for i in z for z in y];;
[%%expect{|
val y : int list list = [[1]]
Line 2, characters 7-8:
2 | true::[i for i in z for z in y];;
           ^
Error: This expression has type int but an expression was expected of type
         bool
|}];;

let y = [[]];;
[i for i in z and z in y];;
[%%expect{|
val y : 'a list list = [[]]
Line 2, characters 12-13:
2 | [i for i in z and z in y];;
                ^
Error: Unbound value z
|}];;

[() for i in [1]];;
[%%expect{|
Line 1, characters 8-9:
1 | [() for i in [1]];;
            ^
Warning 26 [unused-var]: unused variable i.
- : unit list = [()]
|}];;

[|() for i in [|1|]|];;
[%%expect{|
Line 1, characters 9-10:
1 | [|() for i in [|1|]|];;
             ^
Warning 26 [unused-var]: unused variable i.
- : unit array = [|()|]
|}];;

[() for i = 0 to 10] [@warning "+a"];;
[%%expect{|
Line 1, characters 0-20:
1 | [() for i = 0 to 10] [@warning "+a"];;
    ^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : unit list = [(); (); (); (); (); (); (); (); (); (); ()]
|}];;

[|() for i = 0 to 10|] [@warning "+a"];;
[%%expect{|
Line 1, characters 0-22:
1 | [|() for i = 0 to 10|] [@warning "+a"];;
    ^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : unit array = [|(); (); (); (); (); (); (); (); (); (); ()|]
|}];;

(*List construction tests.*)

[i for i = 0 to 10];;
[%%expect{|
- : int list = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
|}];;

[i for i = 10 downto 0];;
[%%expect{|
- : int list = [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 0]
|}];;

let y = [1;2;3];;
[i for i in y];;
[%%expect{|
val y : int list = [1; 2; 3]
- : int list = [1; 2; 3]
|}];;

let y = [0;1;2;3];;
[ (k*4*4 + j*4 + i) for i in y for j in y for k in y];;
[%%expect{|
val y : int list = [0; 1; 2; 3]
- : int list =
[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39;
 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58;
 59; 60; 61; 62; 63]
|}];;

let y = [0;1;2;3];;
[ (k*4*4 + j*4 + i) for i in y and j in y and k in y];;
[%%expect{|
val y : int list = [0; 1; 2; 3]
- : int list =
[0; 16; 32; 48; 4; 20; 36; 52; 8; 24; 40; 56; 12; 28; 44; 60; 1; 17; 33; 49;
 5; 21; 37; 53; 9; 25; 41; 57; 13; 29; 45; 61; 2; 18; 34; 50; 6; 22; 38; 54;
 10; 26; 42; 58; 14; 30; 46; 62; 3; 19; 35; 51; 7; 23; 39; 55; 11; 27; 43;
 59; 15; 31; 47; 63]
|}];;

(*Array construction tests*)

let y = [|0;1;2;3|];;
[| (k*4*4 + j*4 + i) for i in y for j in y for k in y |];;
[%%expect{|
val y : int array = [|0; 1; 2; 3|]
- : int array =
[|0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
  21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39;
  40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58;
  59; 60; 61; 62; 63|]
|}];;

let y = [|0;1;2;3|];;
[| (k*4*4 + j*4 + i) for i in y and j in y and k in y|];;
[%%expect{|
val y : int array = [|0; 1; 2; 3|]
- : int array =
[|0; 16; 32; 48; 4; 20; 36; 52; 8; 24; 40; 56; 12; 28; 44; 60; 1; 17; 33; 49;
  5; 21; 37; 53; 9; 25; 41; 57; 13; 29; 45; 61; 2; 18; 34; 50; 6; 22; 38; 54;
  10; 26; 42; 58; 14; 30; 46; 62; 3; 19; 35; 51; 7; 23; 39; 55; 11; 27; 43;
  59; 15; 31; 47; 63|]
|}];;

let y = [|0;1;2;3|];;
[| (k*4*4 + j*4 + i) for i in y for j in y and k in y|];;
[%%expect{|
val y : int array = [|0; 1; 2; 3|]
- : int array =
[|0; 1; 2; 3; 16; 17; 18; 19; 32; 33; 34; 35; 48; 49; 50; 51; 4; 5; 6; 7; 20;
  21; 22; 23; 36; 37; 38; 39; 52; 53; 54; 55; 8; 9; 10; 11; 24; 25; 26; 27;
  40; 41; 42; 43; 56; 57; 58; 59; 12; 13; 14; 15; 28; 29; 30; 31; 44; 45; 46;
  47; 60; 61; 62; 63|]
|}];;

let y = [|0;1;2;3|];;
[| (k*4*4 + j*4 + i) for i in y and j in y for k in y|];;
[%%expect{|
val y : int array = [|0; 1; 2; 3|]
- : int array =
[|0; 4; 8; 12; 1; 5; 9; 13; 2; 6; 10; 14; 3; 7; 11; 15; 16; 20; 24; 28; 17;
  21; 25; 29; 18; 22; 26; 30; 19; 23; 27; 31; 32; 36; 40; 44; 33; 37; 41; 45;
  34; 38; 42; 46; 35; 39; 43; 47; 48; 52; 56; 60; 49; 53; 57; 61; 50; 54; 58;
  62; 51; 55; 59; 63|]
|}];;


[| (k*4*4 + j*4 + i) for i = 0 to 3 and j = 0 to 3  for k = 0 to 3 |];;
[%%expect{|
- : int array =
[|0; 4; 8; 12; 1; 5; 9; 13; 2; 6; 10; 14; 3; 7; 11; 15; 16; 20; 24; 28; 17;
  21; 25; 29; 18; 22; 26; 30; 19; 23; 27; 31; 32; 36; 40; 44; 33; 37; 41; 45;
  34; 38; 42; 46; 35; 39; 43; 47; 48; 52; 56; 60; 49; 53; 57; 61; 50; 54; 58;
  62; 51; 55; 59; 63|]
|}];;

[| (float_of_int (k*4*4 + j*4 + i)) for i = 0 to 3 and j = 0 to 3  for k = 0 to 3 |];;
[%%expect{|
- : float array =
[|0.; 4.; 8.; 12.; 1.; 5.; 9.; 13.; 2.; 6.; 10.; 14.; 3.; 7.; 11.; 15.; 16.;
  20.; 24.; 28.; 17.; 21.; 25.; 29.; 18.; 22.; 26.; 30.; 19.; 23.; 27.; 31.;
  32.; 36.; 40.; 44.; 33.; 37.; 41.; 45.; 34.; 38.; 42.; 46.; 35.; 39.; 43.;
  47.; 48.; 52.; 56.; 60.; 49.; 53.; 57.; 61.; 50.; 54.; 58.; 62.; 51.; 55.;
  59.; 63.|]
|}];;

let y = [| [| [| 1;2;|]; [| 3;4; |] |]; [| [| 5;6;|]; [| 7;8; |] |] |];;
[| i for i in x for x in z for z in y |];;
[%%expect{|
val y : int array array array =
  [|[|[|1; 2|]; [|3; 4|]|]; [|[|5; 6|]; [|7; 8|]|]|]
- : int array = [|1; 2; 3; 4; 5; 6; 7; 8|]
|}];;

let y = [| [| [| 1;2;|]; [| 3;4; |] |]; [| [| 5;6;|]; [| 7;8; |] |] |];;
[| (i,j) for i in x and j in x for x in z for z in y |];;
[%%expect{|
val y : int array array array =
  [|[|[|1; 2|]; [|3; 4|]|]; [|[|5; 6|]; [|7; 8|]|]|]
- : (int * int) array =
[|(1, 1); (1, 2); (2, 1); (2, 2); (3, 3); (3, 4); (4, 3); (4, 4); (5, 5);
  (5, 6); (6, 5); (6, 6); (7, 7); (7, 8); (8, 7); (8, 8)|]
|}];;

let y = [| [| [| 1;2;|]; [| 3;4; |] |]; [| [| 5;6;|]; [| 7;8; |] |] |];;
[| (string_of_int i,j) for i in x and j in x for x in z for z in y |];;
[%%expect{|
val y : int array array array =
  [|[|[|1; 2|]; [|3; 4|]|]; [|[|5; 6|]; [|7; 8|]|]|]
- : (string * int) array =
[|("1", 1); ("1", 2); ("2", 1); ("2", 2); ("3", 3); ("3", 4); ("4", 3);
  ("4", 4); ("5", 5); ("5", 6); ("6", 5); ("6", 6); ("7", 7); ("7", 8);
  ("8", 7); ("8", 8)|]
|}];;


(*Testcase with empty intermediate array.*)
[|  ( j * 3 + i)  for i = 0 to (j-1) for j = 0 to 2|];;
[%%expect{|
- : int array = [|3; 6; 7|]
|}];;

(* When clauses*)

[(j,i) for j = 0 to i when (i >= 4 && j >= 4) for i = 0 to 9 when (i mod 2 = 0)];;
[%%expect{|
Line 1, characters 67-68:
1 | [(j,i) for j = 0 to i when (i >= 4 && j >= 4) for i = 0 to 9 when (i mod 2 = 0)];;
                                                                       ^
Error: Unbound value i
|}];;

[| (j,i) for j = 0 to i when (i >= 4 && j >= 4) for i = 0 to 9 when (i mod 2 = 0) |];;
[%%expect{|
Line 1, characters 69-70:
1 | [| (j,i) for j = 0 to i when (i >= 4 && j >= 4) for i = 0 to 9 when (i mod 2 = 0) |];;
                                                                         ^
Error: Unbound value i
|}];;

[ (j,i) for j = 0 to i when (i > 4) for i = 0 to 10 when (j = 0) ];;
[%%expect{|
Line 1, characters 58-59:
1 | [ (j,i) for j = 0 to i when (i > 4) for i = 0 to 10 when (j = 0) ];;
                                                              ^
Error: Unbound value j
|}];;

[| (i,j) for i = 0 to 10 when (i mod 2 = 0) for j = 0 to 5 when (j = 1 || j = 2)|];;
[%%expect{|
Line 1, characters 65-66:
1 | [| (i,j) for i = 0 to 10 when (i mod 2 = 0) for j = 0 to 5 when (j = 1 || j = 2)|];;
                                                                     ^
Error: Unbound value j
|}];;

[| (i) for i = 0 to 10 when (i mod 2 = 0)|];;
[%%expect{|
Line 1, characters 29-30:
1 | [| (i) for i = 0 to 10 when (i mod 2 = 0)|];;
                                 ^
Error: Unbound value i
|}];;

[ (i,j,k) for i = 0 to 5 when (i mod 2 = 0)  for j = 0 to 5 when (j mod 2 = 0)  for k = 0 to 5 when (k mod 2 = 0)];;
[%%expect{|
Line 1, characters 101-102:
1 | [ (i,j,k) for i = 0 to 5 when (i mod 2 = 0)  for j = 0 to 5 when (j mod 2 = 0)  for k = 0 to 5 when (k mod 2 = 0)];;
                                                                                                         ^
Error: Unbound value k
|}];;

[| (i,j,k) for i = 0 to 5 when (i mod 2 = 0)  for j = 0 to 5 when (j mod 2 = 0)  for k = 0 to 5 when (k mod 2 = 0)|];;
[%%expect{|
Line 1, characters 102-103:
1 | [| (i,j,k) for i = 0 to 5 when (i mod 2 = 0)  for j = 0 to 5 when (j mod 2 = 0)  for k = 0 to 5 when (k mod 2 = 0)|];;
                                                                                                          ^
Error: Unbound value k
|}];;

[ (i,j,k) for i = 0 to 5  and j = 0 to 5 and k = 0 to 5 when ((k mod 2 = 0) && (i mod 2 = 0) && (j mod 2 = 0))];;
[%%expect{|
Line 1, characters 63-64:
1 | [ (i,j,k) for i = 0 to 5  and j = 0 to 5 and k = 0 to 5 when ((k mod 2 = 0) && (i mod 2 = 0) && (j mod 2 = 0))];;
                                                                   ^
Error: Unbound value k
|}];;

[| (i,j,k) for i = 0 to 5  and j = 0 to 5 and k = 0 to 5 when ((k mod 2 = 0) && (i mod 2 = 0) && (j mod 2 = 0)  )|];;
[%%expect{|
Line 1, characters 64-65:
1 | [| (i,j,k) for i = 0 to 5  and j = 0 to 5 and k = 0 to 5 when ((k mod 2 = 0) && (i mod 2 = 0) && (j mod 2 = 0)  )|];;
                                                                    ^
Error: Unbound value k
|}];;

[| (i,j,k) for i = 0 to 5 when ((k mod 2 = 0) && (i mod 2 = 0) && (j mod 2 = 0)) for j = 0 to 5 for k = 0 to 5 |];;
[%%expect{|
Line 1, characters 50-51:
1 | [| (i,j,k) for i = 0 to 5 when ((k mod 2 = 0) && (i mod 2 = 0) && (j mod 2 = 0)) for j = 0 to 5 for k = 0 to 5 |];;
                                                      ^
Error: Unbound value i
|}];;

let f f =
  [ (f i j k) for i = 0 to 3 when (i mod 2 = 0)  for j = 0 to 3 when (j mod 2 = 0)  for k = 0 to 3 when (k mod 2 = 0)];;
[%%expect{|
Line 2, characters 105-106:
2 |   [ (f i j k) for i = 0 to 3 when (i mod 2 = 0)  for j = 0 to 3 when (j mod 2 = 0)  for k = 0 to 3 when (k mod 2 = 0)];;
                                                                                                             ^
Error: Unbound value k
|}];;

f (fun i j k -> (i,j,k) )
[%%expect{|
Line 1, characters 0-1:
1 | f (fun i j k -> (i,j,k) )
    ^
Error: Unbound value f
|}];;

f (fun i j k -> i )
[%%expect{|
Line 1, characters 0-1:
1 | f (fun i j k -> i )
    ^
Error: Unbound value f
|}];;

f (fun i j k -> float_of_int i )
[%%expect{|
Line 1, characters 0-1:
1 | f (fun i j k -> float_of_int i )
    ^
Error: Unbound value f
|}];;

f (fun i j k -> [|string_of_int i|] )
[%%expect{|
Line 1, characters 0-1:
1 | f (fun i j k -> [|string_of_int i|] )
    ^
Error: Unbound value f
|}];;


(*Make sure stuff is called in correct order/ correct number of times.*)

let var = ref [];;
let f x = var := x::!var; x;;
[%%expect{|
val var : '_weak1 list ref = {contents = []}
val f : '_weak2 -> '_weak2 = <fun>
|}];;

let z = [|1;2;3|];;
[| i  for  i in (f z) |];;
List.rev !var;;
[%%expect{|
val z : int array = [|1; 2; 3|]
- : int array = [|1; 2; 3|]
- : int array list = [[|1; 2; 3|]]
|}];;

var := [];;
let z = [|1;2;3|];;
[| i  for  i in (f z) for i = 0 to 1 |];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int array = [|1; 2; 3|]
Line 3, characters 0-39:
3 | [| i  for  i in (f z) for i = 0 to 1 |];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : int array = [|1; 2; 3; 1; 2; 3|]
- : int array list = [[|1; 2; 3|]; [|1; 2; 3|]]
|}];;

var := [];;
let z = [|1;2;3|];;
[| i  for  i in (f z) for i = 0 to 6 when (i mod 2 = 0) |];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int array = [|1; 2; 3|]
Line 3, characters 43-44:
3 | [| i  for  i in (f z) for i = 0 to 6 when (i mod 2 = 0) |];;
                                               ^
Error: Unbound value i
|}];;

var := [];;
let z = [|1;2;3|];;
[| i  for  i in (f z) and i = 0 to 1 |];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int array = [|1; 2; 3|]
Line 3, characters 0-39:
3 | [| i  for  i in (f z) and i = 0 to 1 |];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : int array = [|1; 1; 2; 2; 3; 3|]
- : int array list = [[|1; 2; 3|]]
|}];;

var := [];;
let z = [|1;2;3|];;
[| i  for  i in (f z) and  i = 0 to 6 when (i mod 2 = 0) |];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int array = [|1; 2; 3|]
Line 3, characters 44-45:
3 | [| i  for  i in (f z) and  i = 0 to 6 when (i mod 2 = 0) |];;
                                                ^
Error: Unbound value i
|}];;

var := [];;
let z = [|[|1;2;3|];[|4;5;6|]|];;
[| i  for  i in (f y) for y in z |];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int array array = [|[|1; 2; 3|]; [|4; 5; 6|]|]
- : int array = [|1; 2; 3; 4; 5; 6|]
- : int array list = [[|1; 2; 3|]; [|4; 5; 6|]]
|}];;


let var = ref [];;
let f x = var := x::!var; x;;
[%%expect{|
val var : '_weak3 list ref = {contents = []}
val f : '_weak4 -> '_weak4 = <fun>
|}];;

let z = [1;2;3];;
[ i  for  i in (f z) ];;
List.rev !var;;
[%%expect{|
val z : int list = [1; 2; 3]
- : int list = [1; 2; 3]
- : int list list = [[1; 2; 3]]
|}];;

var := [];;
let z = [1;2;3];;
[ i  for  i in (f z) for i = 0 to 1 ];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int list = [1; 2; 3]
Line 3, characters 0-37:
3 | [ i  for  i in (f z) for i = 0 to 1 ];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : int list = [1; 2; 3; 1; 2; 3]
- : int list list = [[1; 2; 3]; [1; 2; 3]]
|}];;

var := [];;
let z = [1;2;3];;
[ i  for  i in (f z) for i = 0 to 6 when (i mod 2 = 0) ];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int list = [1; 2; 3]
Line 3, characters 42-43:
3 | [ i  for  i in (f z) for i = 0 to 6 when (i mod 2 = 0) ];;
                                              ^
Error: Unbound value i
|}];;

var := [];;
let z = [1;2;3];;
[ i  for  i in (f z) and i = 0 to 1 ];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int list = [1; 2; 3]
Line 3, characters 0-37:
3 | [ i  for  i in (f z) and i = 0 to 1 ];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable i.
- : int list = [1; 1; 2; 2; 3; 3]
- : int list list = [[1; 2; 3]]
|}];;

var := [];;
let z = [1;2;3];;
[ i  for  i in (f z) and  i = 0 to 6 when (i mod 2 = 0) ];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int list = [1; 2; 3]
Line 3, characters 43-44:
3 | [ i  for  i in (f z) and  i = 0 to 6 when (i mod 2 = 0) ];;
                                               ^
Error: Unbound value i
|}];;

var := [];;
let z = [[1;2;3];[4;5;6]];;
[ i  for  i in (f y) for y in z ];;
List.rev !var;;
[%%expect{|
- : unit = ()
val z : int list list = [[1; 2; 3]; [4; 5; 6]]
- : int list = [1; 2; 3; 4; 5; 6]
- : int list list = [[1; 2; 3]; [4; 5; 6]]
|}];;

let var = ref [];;
let f x = var := x::!var; x;;
[%%expect{|
val var : '_weak5 list ref = {contents = []}
val f : '_weak6 -> '_weak6 = <fun>
|}];;


var := [];;
[ i  for i = (f 0) to (f 5) ];;
List.rev !var;;
[%%expect{|
- : unit = ()
- : int list = [0; 1; 2; 3; 4; 5]
- : int list = [5; 0]
|}];;

var := [];;
[ i  for i = (f 0) to (f 5) and j = (f 3) to (f 4) ];;
List.rev !var;;
[%%expect{|
- : unit = ()
Line 2, characters 0-52:
2 | [ i  for i = (f 0) to (f 5) and j = (f 3) to (f 4) ];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable j.
- : int list = [0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5]
- : int list = [5; 0; 4; 3; 4; 3; 4; 3; 4; 3; 4; 3; 4; 3]
|}];;

var := [];;
[ i  for i = (f 0) to (f 5) for j = (f 3) to (f 4) ];;
List.rev !var;;
[%%expect{|
- : unit = ()
Line 2, characters 0-52:
2 | [ i  for i = (f 0) to (f 5) for j = (f 3) to (f 4) ];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable j.
- : int list = [0; 1; 2; 3; 4; 5; 0; 1; 2; 3; 4; 5]
- : int list = [4; 3; 5; 0; 5; 0]
|}];;

var := [];;
[| i  for i = (f 0) to (f 5) |];;
List.rev !var;;
[%%expect{|
- : unit = ()
- : int array = [|0; 1; 2; 3; 4; 5|]
- : int list = [0; 5]
|}];;

var := [];;
[| i  for i = (f 0) to (f 5) and j = (f 3) to (f 4)  |];;
List.rev !var;;
[%%expect{|
- : unit = ()
Line 2, characters 0-55:
2 | [| i  for i = (f 0) to (f 5) and j = (f 3) to (f 4)  |];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable j.
- : int array = [|0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5|]
- : int list = [0; 5; 3; 4]
|}];;

var := [];;
[| i  for i = (f 0) to (f 5) for j = (f 3) to (f 4)  |];;
List.rev !var;;
[%%expect{|
- : unit = ()
Line 2, characters 0-55:
2 | [| i  for i = (f 0) to (f 5) for j = (f 3) to (f 4)  |];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable j.
- : int array = [|0; 1; 2; 3; 4; 5; 0; 1; 2; 3; 4; 5|]
- : int list = [3; 4; 0; 5; 0; 5]
|}];;

var := [];;
[| i  for i = (f 5) downto (f 0) for j = (f 3) to (f 4) |];;
List.rev !var;;
[%%expect{|
- : unit = ()
Line 2, characters 0-58:
2 | [| i  for i = (f 5) downto (f 0) for j = (f 3) to (f 4) |];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 26 [unused-var]: unused variable j.
- : int array = [|5; 4; 3; 2; 1; 0; 5; 4; 3; 2; 1; 0|]
- : int list = [3; 4; 5; 0; 5; 0]
|}];;
