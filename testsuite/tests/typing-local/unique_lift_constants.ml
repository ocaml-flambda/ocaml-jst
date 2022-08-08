(* TEST
   flags += "-extension unique"
 * expect *)

type point = { dim : int; x : float; y : float; z : float }
[%%expect{|
type point = { dim : int; x : float; y : float; z : float; }
|}]

let update_with_constant (p : point) =
  let q = { unique_ p with dim = 2; x = 2.0; y = 3.0; z = 4.0 } in
  q
[%%expect{|
val update_with_constant : unique_ point -> point = <fun>
|}]

let test =
  let p = { dim = 2; x = 1.0; y = 2.0; z = 3.0 } in
  let q = { dim = 2; x = 1.0; y = 2.0; z = 3.0 } in
  update_with_constant p == update_with_constant q
[%%expect{|
val test : bool = true
|}]

(* Floatblock *)
type fpoint = { x : float; y : float; z : float }
[%%expect{|
type fpoint = { x : float; y : float; z : float; }
|}]

let fupdate_with_constant (p : fpoint) =
  let q = { unique_ p with x = 2.0; y = 3.0; z = 4.0 } in
  q
[%%expect{|
val fupdate_with_constant : unique_ fpoint -> fpoint = <fun>
|}]

let test =
  let p = { x = 1.0; y = 2.0; z = 3.0 } in
  let q = { x = 1.0; y = 2.0; z = 3.0 } in
  fupdate_with_constant p == fupdate_with_constant q
[%%expect{|
val test : bool = true
|}]

let constant_list x =
  x :: 2 :: []
[%%expect{|
val constant_list : int -> int list = <fun>
|}]

let test =
  List.hd (constant_list 1) == List.hd (constant_list 2),
  List.tl (constant_list 1) == List.tl (constant_list 2)
[%%expect{|
val test : bool * bool = (false, true)
|}]

let constant_list_unique x =
  let unique_ y = 2 :: [] in x :: y
[%%expect{|
val constant_list_unique : int -> int list = <fun>
|}]

let test =
  List.hd (constant_list_unique 1) == List.hd (constant_list_unique 2),
  List.tl (constant_list_unique 1) == List.tl (constant_list_unique 2)
[%%expect{|
val test : bool * bool = (false, true)
|}]

let constant_list_unique2 x =
  let unique_ z = [] in
  let unique_ y = 2 :: z in x :: y
[%%expect{|
val constant_list_unique2 : int -> int list = <fun>
|}]

let test =
  List.hd (constant_list_unique2 1) == List.hd (constant_list_unique2 2),
  List.tl (constant_list_unique2 1) == List.tl (constant_list_unique2 2)
[%%expect{|
val test : bool * bool = (false, false)
|}]

let constant_lift b =
  let unique_ p = { x = 1.0; y = 2.0; z = 3.0 } in
  if b then p else { unique_ p with x = 2.0 }
[%%expect{|
val constant_lift : bool -> fpoint = <fun>
|}]

let test =
  ((constant_lift true).x, (constant_lift false).x, (constant_lift true).x)
[%%expect{|
val test : float * float * float = (1., 2., 1.)
|}]
