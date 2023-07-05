(* TEST
   flags += "-extension unique"
 * expect
*)

let unique_use (local_ unique_ _x) = ()
[%%expect{|
val unique_use : local_ unique_ 'a -> unit = <fun>
|}]

let shared_use (local_ x) = ()
[%%expect{|
val shared_use : local_ 'a -> unit = <fun>
|}]

let unique_shared_use (local_ unique_ x) (local_ y) = ()
[%%expect{|
val unique_shared_use : local_ unique_ 'a -> local_ 'b -> unit = <fun>
|}]

let shared_unique_use (local_ x) (local_ unique_ y) = ()
[%%expect{|
val shared_unique_use : local_ 'a -> local_ unique_ 'b -> unit = <fun>
|}]

let shared_shared_use (local_ x) (local_ y) = ()
[%%expect{|
val shared_shared_use : local_ 'a -> local_ 'b -> unit = <fun>
|}]


let shared_global_use x = ()
[%%expect{|
val shared_global_use : 'a -> unit = <fun>
|}]

let local_returning (local_ x) = [%exclave] x
[%%expect{|
val local_returning : local_ 'a -> local_ 'a = <fun>
|}]

(* Let-binding borrowing *)

(* borrowed values are shared and cannot be used as unique *)
let foo () =
  let unique_ y = "hello" in
  let x = & y in
  let _z = unique_ x in
  ()
[%%expect{|
Line 4, characters 19-20:
4 |   let _z = unique_ x in
                       ^
Error: Found a shared value where a unique value was expected
|}]

(* borrowed values are local and cannot escape *)
let foo () =
  let r = ref None in
  let unique_ y = "hello" in
  let x = & y in
  r := Some x;
[%%expect{|
Line 5, characters 12-13:
5 |   r := Some x;
                ^
Error: This value escapes its region
|}]

(* the borrowed value is local to the implicit region; so can't escape whatsoever *)
let foo () =
  let local_ x = "hello" in
  let _z = (let y = & x in
  y
  ) in
  ()
[%%expect{|
Line 4, characters 2-3:
4 |   y
      ^
Error: This local value escapes its region
|}]

(* During borrowing, you are not allowed to use the original value uniquely *)
let foo () =
  let local_ x = "hello" in
  let _z = (let _y = & x in
  unique_use x
  ) in
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 21-22:
3 |   let _z = (let _y = & x in
                         ^

|}]


(* Due to our implementation, borrowing is still counted even if you don't bind
   the borrowed value *)
let foo () =
  let local_ x = "hello" in
  let _z = (let _ = & x in
  unique_use x
  ) in
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 20-21:
3 |   let _z = (let _ = & x in
                        ^

|}]


(* but shared use is fine *)
let foo () =
  let local_ x = "hello" in
  let _z = (let _y = & x in
  shared_use x
  ) in
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* Moreover, that shared use will clash with later unique use *)
let foo () =
  let local_ x = "hello" in
  let _z = (let _y = & x in
  shared_use x
  ) in
  unique_use x;
  ()
[%%expect{|
Line 6, characters 13-14:
6 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 4, characters 13-14:
4 |   shared_use x
                 ^

|}]

(* Usually shared use followed by unique use is error *)
let foo () =
  let local_ x = "hello" in
  shared_use x;
  unique_use x;
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 13-14:
3 |   shared_use x;
                 ^

|}]

(* But if you borrow it for the shared use, it's fine *)
let foo () =
  let local_ x = "hello" in
  (let y = & x in
  shared_use y);
  unique_use x;
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* of course if you still use the original value, it's NOT fine *)
let foo () =
  let local_ x = "hello" in
  (let y = & x in
  shared_use x);
  unique_use x;
  ()
[%%expect{|
Line 5, characters 13-14:
5 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 4, characters 13-14:
4 |   shared_use x);
                 ^

|}]

(* nested borrowing - two regions below,
z cannot escape its region
*)
let foo () =
  let unique_ x = "hello" in
  let y = & x in
  let _ = (let z = & y in z) in
  ()
[%%expect{|
Line 4, characters 26-27:
4 |   let _ = (let z = & y in z) in
                              ^
Error: This local value escapes its region
|}]

(* y can escape *)
let foo () =
  let unique_ x = "hello" in
  let y = & x in
  let _ = (let _z = & y in y) in
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* multiple borrowing in a single let;
share a single region *)
let foo () =
  let unique_ x = "hello" in
  let _ = (let y = & x
  and z = & x in
  y) in
  ()
[%%expect{|
Line 5, characters 2-3:
5 |   y) in
      ^
Error: This local value escapes its region
|}]

(* match borrowing; very similar to let-binding *)

(* borrowed values are shared and cannot be used as unique *)
let foo () =
  let unique_ y = "hello" in
  match & y with
  | x -> let _z = unique_ x in
  ()
[%%expect{|
Line 4, characters 26-27:
4 |   | x -> let _z = unique_ x in
                              ^
Error: Found a shared value where a unique value was expected
|}]

(* borrowed values are local and cannot escape *)
let foo () =
  let r = ref None in
  let unique_ y = "hello" in
  match & y with
  | x -> r := Some x;
[%%expect{|
Line 5, characters 19-20:
5 |   | x -> r := Some x;
                       ^
Error: This value escapes its region
|}]

(* the borrowed value is local to the implicit region; so can't escape whatsoever *)
let foo () =
  let local_ x = "hello" in
  let _z = (match & x with
  | y -> y
  ) in
  ()
[%%expect{|
Line 4, characters 9-10:
4 |   | y -> y
             ^
Error: This local value escapes its region
|}]

(* During borrowing, you are not allowed to use the original value uniquely *)
let foo () =
  let local_ x = "hello" in
  let _z = (match & x with
  | _y -> unique_use x
  ) in
  ()
[%%expect{|
Line 4, characters 21-22:
4 |   | _y -> unique_use x
                         ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 18-19:
3 |   let _z = (match & x with
                      ^

|}]


(* Due to our implementation, borrowing is still counted even if you don't
really bind the borrowed value *)
let foo () =
  let local_ x = "hello" in
  let _z = (match & x with
  | _ -> unique_use x
  ) in
  ()
[%%expect{|
Line 4, characters 20-21:
4 |   | _ -> unique_use x
                        ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 18-19:
3 |   let _z = (match & x with
                      ^

|}]

(* but shared use is fine *)
let foo () =
  let local_ x = "hello" in
  let _z = (match & x with
  | _ -> shared_use x
  ) in
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* Moreover, that shared use will clash with later unique use *)
let foo () =
  let local_ x = "hello" in
  let _z = (match & x with
  | _ -> shared_use x
  ) in
  unique_use x;
  ()
[%%expect{|
Line 6, characters 13-14:
6 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 4, characters 20-21:
4 |   | _ -> shared_use x
                        ^

|}]

(* Usually shared use followed by unique use is error *)
let foo () =
  let local_ x = "hello" in
  shared_use x;
  unique_use x;
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 13-14:
3 |   shared_use x;
                 ^

|}]

(* But if you borrow it for the shared use, it's fine *)
let foo () =
  let local_ x = "hello" in
  (match & x with
  | y -> shared_use y);
  unique_use x;
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* of course if you still use the original value, it's NOT fine *)
let foo () =
  let local_ x = "hello" in
  (match & x with
  | _ -> shared_use x);
  unique_use x;
  ()
[%%expect{|
Line 5, characters 13-14:
5 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 4, characters 20-21:
4 |   | _ -> shared_use x);
                        ^

|}]

(* nested borrowing - two regions below,
z cannot escape its region
*)
let foo () =
  let unique_ x = "hello" in
  match & x with
  | y -> let _ = (match & y with |z -> z) in
  ()
[%%expect{|
Line 4, characters 39-40:
4 |   | y -> let _ = (match & y with |z -> z) in
                                           ^
Error: This local value escapes its region
|}]

(* y can escape *)
let foo () =
  let unique_ x = "hello" in
  match & x with
  | y -> let _ = (match & y with | _z ->  y) in
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* function application borrowing *)

(* You can't use x uniquely after shared usage *)
let foo () =
  let unique_ x = "hello" in
  shared_use x;
  unique_use x;
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 13-14:
3 |   shared_use x;
                 ^

|}]

(* unless if you borrow it *)
let foo () =
  let unique_ x = "hello" in
  shared_use &x;
  unique_use x;
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* borrow after unique usage is bad *)
let foo () =
  let unique_ x = "hello" in
  unique_use x;
  shared_use &x;
  ()
[%%expect{|
Line 3, characters 13-14:
3 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 4, characters 13-14:
4 |   shared_use &x;
                 ^

|}]

(* multiple borrowing is fine *)
let foo () =
  let unique_ x = "hello" in
  shared_shared_use &x &x;
  unique_use x;
  ()
[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* but you need to borrow both of course *)
let foo () =
  let unique_ x = "hello" in
  shared_shared_use &x x;
  unique_use x;
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 23-24:
3 |   shared_shared_use &x x;
                           ^

|}]

(* a tricky case *)
let foo () =
  let unique_ x = "hello" in
  shared_use (& (shared_use x));
  unique_use x;
  ()
[%%expect{|
Line 4, characters 13-14:
4 |   unique_use x;
                 ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 28-29:
3 |   shared_use (& (shared_use x));
                                ^

|}]



(* borrowed values are shared *)
let foo () =
  let unique_ x = "hello" in
  unique_use &x;
  ()
[%%expect{|
Line 3, characters 13-15:
3 |   unique_use &x;
                 ^^
Error: Found a shared value where a unique value was expected
|}]

(* borrowed values are local and cannot escape *)
let foo () =
  let unique_ x = "hello" in
  shared_global_use &x;
  ()
[%%expect{|
Line 3, characters 20-22:
3 |   shared_global_use &x;
                        ^^
Error: This value escapes its region
|}]

(* Borrowing doesn't work well with local-returning functions *)
let foo () =
  let unique_ x = "hello" in
  local_returning &x;
  ()
[%%expect{|
Line 3, characters 2-20:
3 |   local_returning &x;
      ^^^^^^^^^^^^^^^^^^
Error: This local value escapes its region
|}]

let foo () =
  let unique_ x = "hello" in
  shared_unique_use &x x;
  ()
[%%expect{|
Line 3, characters 23-24:
3 |   shared_unique_use &x x;
                           ^
Error: This is used uniquely here so cannot be used twice.  Another use is
Line 3, characters 20-21:
3 |   shared_unique_use &x x;
                        ^

|}]
