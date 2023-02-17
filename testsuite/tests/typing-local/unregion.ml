(* TEST
 * expect *)

(* typing tests *)

let escape x =
  let _ = ref x in
  ()
[%%expect{|
val escape : 'a -> unit = <fun>
|}]  

(* Any function ending with unregion is always typed to 
   return local value. 
  This is to accomadate some code in compiler that relies 
  on the function's type to know if it allocates in caller's 
  region. *)
let foo () = 
  [%unregion] (
    let local_ y = Some 42 in 
    y
  )
[%%expect{|
val foo : unit -> local_ int option = <fun>
|}]
(* sidenote: in the above, 
   y escapes the function even though local_
   - indeed y is in the outer region!
   *)

(* Of course this applies even when the unregion returns a global value,
  because it might still allocate in outer region
    *)
let foo () = 
  [%unregion] (
    let local_ _y = Some 42 in 
    let x = Some 42 in 
    let _ = escape x in 
    x
  )
[%%expect{|
val foo : unit -> local_ int option = <fun>
|}]

(* this still applies even when the unregion doesn't allocate in outer region at all,
  because I don't know any reliable mechanisms in type checker to do that. 
  So it's better to be safe and say that "it might allocate in outer region". *)
let foo x =
  [%unregion] (
    let x = Some 42 in 
    let _ = escape x in
    x
  )
[%%expect{|
val foo : 'a -> local_ int option = <fun>
|}]


(* Below we do some usual testing  *)
let foo x =
  [%unregion] (
    let local_ y = None in
    (* y is not global *)
    ref y
  )
[%%expect{|
Line 5, characters 8-9:
5 |     ref y
            ^
Error: This value escapes its region
|}]

(* following we check error detection *)
let foo x =
  let local_ y = "foo" in
  [%unregion] (Some y)
[%%expect{|
Line 3, characters 20-21:
3 |   [%unregion] (Some y)
                        ^
Error: The value y is local, so cannot be used inside unregion
|}]

let foo x =
  let local_ y = "foo" in
  let z = [%unregion] (Some y) in
  z
[%%expect{|
Line 3, characters 10-30:
3 |   let z = [%unregion] (Some y) in
              ^^^^^^^^^^^^^^^^^^^^
Error: Unregion expression should only be in tail position of the current region
|}]

(* following we test WHILE loop *)
(* unregion in loop is allowed*)
let foo () =
  while true do
    [%unregion] ()
  done

[%%expect{|
val foo : unit -> unit = <fun>
|}]

(* we also require tail position *)
let foo () =
  while true do
    [%unregion] ();
    ()
  done
[%%expect{|
Line 3, characters 4-18:
3 |     [%unregion] ();
        ^^^^^^^^^^^^^^
Error: Unregion expression should only be in tail position of the current region
|}]

(* following we test FOR loop *)
let foo () =
  for i = 1 to 42 do
    [%unregion] ()
  done
[%%expect{|
val foo : unit -> unit = <fun>
|}]

let foo () =
  for i = 1 to 42 do
    [%unregion] ();
    ()
  done
[%%expect{|
Line 3, characters 4-18:
3 |     [%unregion] ();
        ^^^^^^^^^^^^^^
Error: Unregion expression should only be in tail position of the current region
|}]

type t = { nonlocal_ x : int option }

let foo (local_ x) =
  let __ = { x } in
  [%unregion] x

[%%expect{|
type t = { nonlocal_ x : int option; }
val foo : local_ int option -> local_ int option = <fun>
|}]

let foo (local_ x) =
  let _ = { x } in
  [%unregion] { x }

[%%expect{|
Line 3, characters 16-17:
3 |   [%unregion] { x }
                    ^
Error: This local value escapes its region
|}]

(* semantics tests *)

type data = {mutable a : string}

let foo () =
  let local_ x : data = {a  = "foo"} in
  let local_ z = "hello" in
  x.a <- z;
  while true do
    [%unregion] (
      let local_ y = "hello" in
      x.a <- y
    )
  done

[%%expect{|
type data = { mutable a : string; }
Line 6, characters 9-10:
6 |   x.a <- z;
             ^
Error: This value escapes its region
|}]

let foo x =
  [%unregion] (
    let local_ y = Some x in
    y
  );;

let bar _ =
  match foo 5 with
  | None -> "None!"
  | Some x -> "Some of " ^ (string_of_int (x + 0)) ;;
bar ();;
[%%expect{|
val foo : 'a -> local_ 'a option = <fun>
val bar : 'a -> string = <fun>
- : string = "Some of 5"
|}]

