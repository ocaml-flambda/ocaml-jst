(* TEST
  flags = "-extension include_functor"
   * expect
*)

(* Test 1: Basic usage in structs *)
module type S = sig
  type t
  val x : t
end

module F1 (X : S) = struct
  let y = X.x
end

module M1 = struct
  type t = int
  let x = 5

  include functor F1
end

let () = assert Int.(equal M1.y 5);;
[%%expect{|
module type S = sig type t val x : t end
module F1 : functor (X : S) -> sig val y : X.t end
module M1 : sig type t = int val x : int val y : int end
|}];;

(* Test 2: Wrong type in structure *)
module M2 = struct
  type t = int
  let x = true

  include functor F1
end;;
[%%expect{|
Line 5, characters 18-20:
5 |   include functor F1
                      ^^
Error: Signature mismatch in included functor's parameter:
       Values do not match: val x : bool is not included in val x : t
|}];;

(* Test 3: Missing type in structure *)
module M3 = struct
  let x = 5

  include functor F1
end;;
[%%expect{|
Line 4, characters 18-20:
4 |   include functor F1
                      ^^
Error: Signature mismatch in included functor's parameter:
       The type `t' is required but not provided
|}];;

(* Test 4: Missing value in structure *)
module M4 = struct
  type t = int
  let y = 5

  include functor F1
end;;
[%%expect{|
Line 5, characters 18-20:
5 |   include functor F1
                      ^^
Error: Signature mismatch in included functor's parameter:
       The value `x' is required but not provided
|}];;

(* Test 5: Include functor in signature *)
module type T = sig
  type s
  val f : s -> bool
end

module type F5 = functor (X : S) -> T with type s = X.t

module type M5_sig = sig
  type t
  val x : t

  include functor F5
end

module M5_impl : M5_sig = struct
  type t = int
  type s = t

  let x = 5
  let f s = x = s
end
let () = assert (M5_impl.f M5_impl.x);;
[%%expect{|
module type T = sig type s val f : s -> bool end
module type F5 = functor (X : S) -> sig type s = X.t val f : s -> bool end
module type M5_sig = sig type t val x : t type s = t val f : s -> bool end
module M5_impl : M5_sig
|}];;

(* Test 6: Wrong type in signature *)
module type M6_sig = sig
  type t
  val x : bool

  include functor F5
end;;
[%%expect{|
Line 5, characters 18-20:
5 |   include functor F5
                      ^^
Error: Signature mismatch in included functor's parameter:
       Values do not match: val x : bool is not included in val x : t
|}];;

(* Test 7: Missing type in signature *)
module type M7_sig = sig
  val x : bool

  include functor F5
end;;
[%%expect{|
Line 4, characters 18-20:
4 |   include functor F5
                      ^^
Error: Signature mismatch in included functor's parameter:
       The type `t' is required but not provided
|}];;

(* Test 8: Missing val in signature *)
module type M8_sig = sig
  type t

  include functor F5
end;;
[%%expect{|
Line 4, characters 18-20:
4 |   include functor F5
                      ^^
Error: Signature mismatch in included functor's parameter:
       The value `x' is required but not provided
|}];;

(* Test 9: Nested module names work *)
module type Eq9 = sig
  type t
  val z : t
  val equal : t -> t -> bool
end

module type S9 = sig
  module Foo : Eq9
end

module F9 (X : S9) = struct
  let eq_z = X.Foo.equal X.Foo.z
end

module M9 = struct
  module Foo : Eq9 = struct
    include Int
    let z = 7
  end
  include functor F9
end

let () = assert (M9.eq_z M9.Foo.z);;
[%%expect{|
module type Eq9 = sig type t val z : t val equal : t -> t -> bool end
module type S9 = sig module Foo : Eq9 end
module F9 : functor (X : S9) -> sig val eq_z : X.Foo.t -> bool end
module M9 : sig module Foo : Eq9 val eq_z : Foo.t -> bool end
|}];;

let () = assert (M9.eq_z 7);;
[%%expect{|
Line 1, characters 25-26:
1 | let () = assert (M9.eq_z 7);;
                             ^
Error: This expression has type int but an expression was expected of type
         M9.Foo.t
|}];;

module M9' = struct
  module Foo : Eq9 with type t = int = struct
    include Int
    let z = 6
  end
  include functor F9
end

let () = assert (not (M9'.eq_z 5))
let () = assert (M9'.eq_z 6);;
[%%expect{|
module M9' :
  sig
    module Foo : sig type t = int val z : t val equal : t -> t -> bool end
    val eq_z : int -> bool
  end
|}];;

(* Test 10: nondep_supertype: Get good error if we need a name for the
   parameter. *)
module F10 (X : Set.OrderedType) = struct
  let s : Set.Make(X).t = assert false
end

module M10 = struct
  type t = T
  let compare _ _ = 0
  include functor F10
end;;
[%%expect{|
module F10 : functor (X : Set.OrderedType) -> sig val s : Set.Make(X).t end
Line 8, characters 18-21:
8 |   include functor F10
                      ^^^
Error: This functor has type
       functor (X : Set.OrderedType) -> sig val s : Set.Make(X).t end
       The parameter cannot be eliminated in the result type.
       This functor can't be included directly; please apply it to an explicit argument.
|}];;

(* Test 11: Include functor should work at the toplevel (and check shadowing). *)
type t = int
let x : t = 3
let x : t = 5
include functor F1

let () = assert (Int.(equal y 5));;
[%%expect{|
type t = int
val x : t = 3
val x : t = 5
val y : int = 5
|}];;

type t = int
let x : t = 5
let x : t = 3
include functor F1

let () = assert (Int.(equal y 5));;
[%%expect{|
type t = int
val x : t = 5
val x : t = 3
val y : int = 3
Exception: Assert_failure ("", 6, 9).
|}]

(* Test 12: Check that things get marked used appropriately when they are
   used by include functor *)
module M12 : sig val y : int list end = struct
  module Bar = struct
    type t = int
    let x = 5
    let q = "foo"
  end

  module F (G :
    sig
      module T_sub : sig type t val x : t end
                  -> sig type t val x : t end
    end) = struct
    module Foo = G.T_sub(Bar)
    let y = Foo.x
  end

  module T_sub (X : sig type t val x : t end) = struct
    type t = X.t list
    let x = [X.x]
    let z = "something"
  end
  include functor F
end;;
[%%expect{|
module M12 : sig val y : int list end
|}];;


(* Test 13: Check that we reject uses in recursive module signatures *)
module type S13 = sig val foo : int end

module type F13 = functor (X : S) -> S13

module rec G : sig
  type t
  val x : t
  include functor F13
end = struct
  type t = int
  let x = 3
  let foo = x
end;;
[%%expect{|
module type S13 = sig val foo : int end
module type F13 = functor (X : S) -> S13
Line 8, characters 2-21:
8 |   include functor F13
      ^^^^^^^^^^^^^^^^^^^
Error: Including a functor is not supported in recursive module signatures
|}];;

(* Test 14: Check that we reject including a functor with multiple arguments *)
module F14 (X : S) (Y : S) = struct
  let z = (X.x, Y.x)
end

module M14 = struct
  type t = int
  let x : t = 5

  include functor F14
end;;
[%%expect{|
module F14 : functor (X : S) (Y : S) -> sig val z : X.t * Y.t end
Line 9, characters 18-21:
9 |   include functor F14
                      ^^^
Error: Functors with multiple arguments can not be included directly.
       This functor has type
       functor (X : S) (Y : S) -> sig val z : X.t * Y.t end
       Please apply it to explicit arguments instead.
|}];;

