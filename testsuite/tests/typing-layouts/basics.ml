(* TEST
   * expect
*)
type t_any   [@@any]
type t_value [@@value]
type t_imm   [@@immediate]
type t_imm64 [@@immediate64]
type t_void  [@@void]

type void_variant = VV of t_void
type void_record = {vr_void : t_void; vr_int : int}
type void_unboxed_record = { vur_void : t_void } [@@unboxed]


[%%expect{|
type t_any [@@any]
type t_value [@@value]
type t_imm [@@immediate]
type t_imm64 [@@immediate64]
type t_void [@@void]
type void_variant = VV of t_void
type void_record = { vr_void : t_void; vr_int : int; }
type void_unboxed_record = { vur_void : t_void; } [@@unboxed]
|}];;

(*************************************************)
(* Test 1: Reject non-value function arg/returns *)
module type S = sig
  val f : t_any -> int
end;;
[%%expect {|
Line 2, characters 10-15:
2 |   val f : t_any -> int
              ^^^^^
Error: Function argument types must have layout value.
        t_any has layout any, which is not a sublayout of value.
|}]

module type S = sig
  val f : int -> t_void
end;;
[%%expect {|
Line 2, characters 17-23:
2 |   val f : int -> t_void
                     ^^^^^^
Error: Function return types must have layout value.
        t_void has layout void, which is not a sublayout of value.
|}];;

module type S = sig
  val f : void_unboxed_record -> int
end
[%%expect {|
Line 2, characters 10-29:
2 |   val f : void_unboxed_record -> int
              ^^^^^^^^^^^^^^^^^^^
Error: Function argument types must have layout value.
        void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module type S = sig
  val f : int -> void_unboxed_record
end
[%%expect {|
Line 2, characters 17-36:
2 |   val f : int -> void_unboxed_record
                     ^^^^^^^^^^^^^^^^^^^
Error: Function return types must have layout value.
        void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module type S = sig
  type t [@@void]

  type s = r -> int
  and r = t
end;;
[%%expect{|
Line 5, characters 2-11:
5 |   and r = t
      ^^^^^^^^^
Error:
       r has layout void, which is not a sublayout of value.
|}]

module type S = sig
  type t [@@void]

  type 'a s = 'a -> int constraint 'a = t
end;;
[%%expect{|
Line 4, characters 35-41:
4 |   type 'a s = 'a -> int constraint 'a = t
                                       ^^^^^^
Error: The type constraints are not consistent.
       Type ('a : value) is not compatible with type t
       t has layout void, which is not a sublayout of value.
|}]

(* CJC XXX errors: the F1 and F1' errors should ideally mention that the layout
   restriction is coming from the function type *)
module F1 (X : sig val x : t_void end) = struct
  let f () = X.x
end;;
[%%expect{|
Line 2, characters 13-16:
2 |   let f () = X.x
                 ^^^
Error: This expression has type t_void but an expression was expected of type
         ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

module F1 (X : sig val f : void_record -> unit end) = struct
  let g z = X.f { vr_void = z; vr_int = 42 }
end;;
[%%expect{|
Line 2, characters 28-29:
2 |   let g z = X.f { vr_void = z; vr_int = 42 }
                                ^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

(*********************************************)
(* Test 2: Permit value function arg/returns *)
module type S = sig
  val f1 : t_value -> t_value
  val f2 : t_imm -> t_imm64
end;;

[%%expect{|
module type S = sig val f1 : t_value -> t_value val f2 : t_imm -> t_imm64 end
|}];;

(**************************************)
(* Test 3: basic annotated parameters *)
type 'a [@immediate] imm_id = 'a

[%%expect{|
type 'a imm_id = 'a
|}];;

type my_int = int imm_id
let plus_3 (x : my_int) = x + 3
let plus_3' (x : int imm_id) = x + 3;;

[%%expect{|
type my_int = int imm_id
val plus_3 : my_int -> int = <fun>
val plus_3' : int imm_id -> int = <fun>
|}];;

let string_id (x : string imm_id) = x;;
[%%expect{|
Line 1, characters 19-25:
1 | let string_id (x : string imm_id) = x;;
                       ^^^^^^
Error: This type string should be an instance of type ('a : immediate)
       string has layout value, which is not a sublayout of immediate.
|}];;

let id_for_imms (x : 'a imm_id) = x

let three = id_for_imms 3
let true_ = id_for_imms true;;
[%%expect{|
val id_for_imms : 'a imm_id -> 'a imm_id = <fun>
val three : int imm_id = 3
val true_ : bool imm_id = true
|}]

let not_helloworld = id_for_imms "hello world";;
[%%expect{|
Line 1, characters 33-46:
1 | let not_helloworld = id_for_imms "hello world";;
                                     ^^^^^^^^^^^^^
Error: This expression has type string but an expression was expected of type
         'a imm_id = ('a : immediate)
       string has layout value, which is not a sublayout of immediate.
|}]

(************************************)
(* Test 4: parameters and recursion *)
type 'a [@immediate] t4
and s4 = string t4;;

[%%expect{|
Line 2, characters 9-15:
2 | and s4 = string t4;;
             ^^^^^^
Error: This type string should be an instance of type ('a : immediate)
       string has layout value, which is not a sublayout of immediate.
|}];;

type s4 = string t4
and 'a [@immediate] t4;;

[%%expect{|
Line 1, characters 10-16:
1 | type s4 = string t4
              ^^^^^^
Error: This type string should be an instance of type ('a : immediate)
       string has layout value, which is not a sublayout of immediate.
|}]

type s4 = int t4
and 'a [@immediate] t4;;

[%%expect{|
type s4 = int t4
and 'a t4
|}]

type s4 = s5 t4
and 'a [@immediate] t4
and s5 = int;;

[%%expect{|
type s4 = s5 t4
and 'a t4
and s5 = int
|}]

type s4 = s5 t4
and 'a [@immediate] t4
and s5 = string;;

[%%expect{|
Line 3, characters 0-15:
3 | and s5 = string;;
    ^^^^^^^^^^^^^^^
Error:
       s5 has layout value, which is not a sublayout of immediate.
|}]
(* CJC XXX errors: improve error *)

type 'a [@any] t4 = 'a
and s4 = string t4;;
[%%expect{|
type 'a t4 = 'a
and s4 = string t4
|}];;

type s4 = string t4
and 'a [@any] t4;;
[%%expect{|
type s4 = string t4
and 'a t4
|}];;

(************************************************************)
(* Test 4: You can touch a void, but not return it directly *)
type 'a [@void] void4 = Void4  of 'a
type 'a [@any] any4 = Any4 of 'a

let id4 : 'a void4 -> 'a void4 = function
  | Void4 x -> Void4 x

(* CR ccasinghino: At the moment, the code in the comment below does not work.
   Because we demand that constructor arguments have layout (Sort 'l), the type
   [any4] actually only works on values.

   In the future, we would like to allow constructors to take arguments of any
   layout and instead restrict how those arguments are used.  In that case, the
   below functions will work (though only on for ('a : void)).
*)
(* let f4 : 'a void4 -> 'a any4 = function
 *     Void4 x -> Any4 x
 *
 * let g4 : 'a any4 -> 'a void4 = function
 *   Any4 x -> Void4 x
 * ;; *)

[%%expect{|
type 'a void4 = Void4 of 'a
type 'a any4 = Any4 of 'a
val id4 : 'a void4 -> 'a void4 = <fun>
|}];;


(* disallowed attempts to use f4 and Void4 on non-voids *)
let h4 (x : int void4) = f4 x
[%%expect{|
Line 1, characters 12-15:
1 | let h4 (x : int void4) = f4 x
                ^^^
Error: This type int should be an instance of type ('a : void)
       int has layout immediate, which is not a sublayout of void.
|}];;

let h4' (x : int any4) = Void4 x
[%%expect{|
Line 1, characters 31-32:
1 | let h4' (x : int any4) = Void4 x
                                   ^
Error: This expression has type int any4
       but an expression was expected of type ('a : void)
       int any4 has layout value, which is not a sublayout of void.
|}];;

(* disallowed - tries to return void *)
let g (x : 'a void4) =
  match x with
  | Void4 x -> x;;
[%%expect{|
Line 3, characters 15-16:
3 |   | Void4 x -> x;;
                   ^
Error: This expression has type ('a : void)
       but an expression was expected of type ('b : value)
       'a has layout value, which does not overlap with void.
|}, Principal{|
Lines 2-3, characters 2-16:
2 | ..match x with
3 |   | Void4 x -> x..
Error: This expression has type ('a : void)
       but an expression was expected of type ('b : value)
       'a has layout value, which does not overlap with void.
|}]
(* CJC XXX errors: understand what's going on with Principal mode here (and improve
   error messages generally *)

(****************************************)
(* Test 5: explicitly polymorphic types *)
type ('a : immediate) t5_imm = T5imm of 'a
type ('a : value) t5_val = T5val of 'a;;
[%%expect{|
type 'a t5_imm = T5imm of 'a
type 'a t5_val = T5val of 'a
|}];;

let ignore_val5 : 'a . 'a -> unit =
  fun a -> let _ = T5val a in ();;
[%%expect{|
val ignore_val5 : 'a -> unit = <fun>
|}];;

let ignore_imm5 : 'a . 'a -> unit =
  fun a -> let _ = T5imm a in ();;
[%%expect{|
Line 2, characters 2-32:
2 |   fun a -> let _ = T5imm a in ();;
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This definition has type 'b -> unit which is less general than
         'a. 'a -> unit
       'a has layout value, which is not a sublayout of immediate.
|}];;

let o5 = object
  method ignore_imm5 : 'a . 'a -> unit =
    fun a -> let _ = T5imm a in ()
end;;
[%%expect{|
Line 3, characters 4-34:
3 |     fun a -> let _ = T5imm a in ()
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This method has type 'b -> unit which is less general than
         'a. 'a -> unit
       'a has layout value, which is not a sublayout of immediate.
|}];;

(* CJC XXX add more tests here once you can annotate these types with layouts *)

(*****************************************)
(* Test 6: the layout check in unify_var *)
type 'a [@immediate] t6 = Foo6 of 'a

type t6' = (int * int) t6;;
[%%expect{|
type 'a t6 = Foo6 of 'a
Line 3, characters 12-21:
3 | type t6' = (int * int) t6;;
                ^^^^^^^^^
Error: This type int * int should be an instance of type ('a : immediate)
       int * int has layout value, which is not a sublayout of immediate.
|}]

(**********************************************************)
(* Test 7: Polymorphic variants take value args (for now) *)

(* CR layouts: we'll eventually allow non-value arguments to polymorphic
   variants *)
module M7_1 = struct
  type foo1 = [ `Foo1 of int | `Baz1 of t_void | `Bar1 of string ];;
end
[%%expect{|
Line 2, characters 40-46:
2 |   type foo1 = [ `Foo1 of int | `Baz1 of t_void | `Bar1 of string ];;
                                            ^^^^^^
Error: Polymorpic variant constructor argument types must have layout value.
        t_void has layout void, which is not a sublayout of value.
|}];;

module M7_2 = struct
  type t = { v : t_void } [@@unboxed]
  type result = V of t | I of int

  let foo x =
    match x with
    | `Baz 42 -> I 53
    | `Bar v -> { v }
    | `Bas i -> I i
end;;
[%%expect {|
Line 8, characters 16-21:
8 |     | `Bar v -> { v }
                    ^^^^^
Error: This expression should not be a record, the expected type is result
|}, Principal{|
Line 8, characters 18-19:
8 |     | `Bar v -> { v }
                      ^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

module M7_3 = struct
  type 'a t = [ `Foo of 'a | `Baz of int ]

  type bad = t_void t
end;;
[%%expect {|
Line 4, characters 13-19:
4 |   type bad = t_void t
                 ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

module M7_4 = struct
  type 'a t = [ `Foo of 'a | `Baz of int ] constraint 'a = void_unboxed_record
end;;
[%%expect {|
Line 2, characters 54-78:
2 |   type 'a t = [ `Foo of 'a | `Baz of int ] constraint 'a = void_unboxed_record
                                                          ^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
       Type ('a : value) is not compatible with type void_unboxed_record
       void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module type S7_5 = sig
  val x : [`A of t_void]
end;;
[%%expect{|
Line 2, characters 17-23:
2 |   val x : [`A of t_void]
                     ^^^^^^
Error: Polymorpic variant constructor argument types must have layout value.
        t_void has layout void, which is not a sublayout of value.
|}]


(************************************************)
(* Test 8: Tuples only work on values (for now) *)

(* CR layouts v5: these should work *)
module M8_1 = struct
  type foo1 = int * t_void * [ `Foo1 of int | `Bar1 of string ];;
end
[%%expect{|
Line 2, characters 20-26:
2 |   type foo1 = int * t_void * [ `Foo1 of int | `Bar1 of string ];;
                        ^^^^^^
Error: Tuple element types must have layout value.
        t_void has layout void, which is not a sublayout of value.
|}];;

module M8_2 = struct
  type result = V of (string * void_unboxed_record) | I of int
end;;
[%%expect {|
Line 2, characters 31-50:
2 |   type result = V of (string * void_unboxed_record) | I of int
                                   ^^^^^^^^^^^^^^^^^^^
Error: Tuple element types must have layout value.
        void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module M8_3 = struct
  type s = V of void_unboxed_record | I of int

  let foo x =
    match x with
    | I _ -> assert false
    | V t -> t, 27
end;;
[%%expect {|
Line 7, characters 13-14:
7 |     | V t -> t, 27
                 ^
Error: This expression has type void_unboxed_record
       but an expression was expected of type ('a : value)
       void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module M8_4 = struct
  let foo x =
    match x with
    | ({vur_void = _},i) -> i
end;;
[%%expect {|
Line 4, characters 8-16:
4 |     | ({vur_void = _},i) -> i
            ^^^^^^^^
Error: The record field vur_void belongs to the type void_unboxed_record
       but is mixed here with fields of type ('a : value)
       void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module M8_5 = struct
  type 'a t = (int * 'a)

  type bad = t_void t
end;;
[%%expect {|
Line 4, characters 13-19:
4 |   type bad = t_void t
                 ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

module M8_6 = struct
  type 'a t = int * 'a constraint 'a = void_unboxed_record
end;;
[%%expect {|
Line 2, characters 34-58:
2 |   type 'a t = int * 'a constraint 'a = void_unboxed_record
                                      ^^^^^^^^^^^^^^^^^^^^^^^^
Error: The type constraints are not consistent.
       Type ('a : value) is not compatible with type void_unboxed_record
       void_unboxed_record has layout void, which is not a sublayout of value.
|}];;

module type S8_7 = sig
  val x : int * t_void
end;;
[%%expect{|
Line 2, characters 16-22:
2 |   val x : int * t_void
                    ^^^^^^
Error: Tuple element types must have layout value.
        t_void has layout void, which is not a sublayout of value.
|}];;

module M8_9 (X : sig
    val vr : void_record
  end) =
struct
  match 3, X.vr.vr_void with
  | _ -> 42
end;;
[%%expect {|
Line 5, characters 11-23:
5 |   match 3, X.vr.vr_void with
               ^^^^^^^^^^^^
Error: This expression has type t_void but an expression was expected of type
         ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

(*************************************************)
(* Test 9: layouts are checked by "more general" *)

(* This hits the first linktype in moregen (no expansion required to see it's a
   var) *)
module M9_1 : sig
  val x : string
end = struct
  type ('a : immediate) t = 'a

  let f : 'a t -> 'a = fun x -> x

  let x = f (assert false)
end;;
[%%expect {|
Lines 3-9, characters 6-3:
3 | ......struct
4 |   type ('a : immediate) t = 'a
5 |
6 |   let f : 'a t -> 'a = fun x -> x
7 |
8 |   let x = f (assert false)
9 | end..
Error: Signature mismatch:
       Modules do not match:
         sig type 'a t = 'a val f : 'a t -> 'a val x : 'a end
       is not included in
         sig val x : string end
       Values do not match: val x : 'a is not included in val x : string
       The type string is not compatible with the type string
       string has layout value, which is not a sublayout of immediate.
|}];;

(* This hits the second linktype in moregen (requires expansion to see it's a
   var) *)
module M9_2 : sig
  val x : string
end = struct
  type ('a : immediate) t = 'a

  let f (x : 'a t) : 'a t = x

  let x = f (assert false)
end;;
[%%expect {|
Lines 3-9, characters 6-3:
3 | ......struct
4 |   type ('a : immediate) t = 'a
5 |
6 |   let f (x : 'a t) : 'a t = x
7 |
8 |   let x = f (assert false)
9 | end..
Error: Signature mismatch:
       Modules do not match:
         sig type 'a t = 'a val f : 'a t -> 'a t val x : 'a t end
       is not included in
         sig val x : string end
       Values do not match: val x : 'a t is not included in val x : string
       The type string t = string is not compatible with the type string
       string has layout value, which is not a sublayout of immediate.
|}]

(**************************************************************)
(* Test 10: objects are values and methods take/return values *)
module M10_1 = struct
  type ('a : void) t = { x : int; v : 'a }

  let f t =
    t.v # baz10
end;;
[%%expect{|
Line 5, characters 4-7:
5 |     t.v # baz10
        ^^^
Error: Methods must have layout value.
       This expression has layout void, which does not overlap with value.
|}]

module M10_2 = struct
  let foo x = VV (x # getvoid)
end;;
[%%expect{|
Line 2, characters 17-30:
2 |   let foo x = VV (x # getvoid)
                     ^^^^^^^^^^^^^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

module M10_3 = struct
  type ('a : void) t = A of 'a

  let foo o (A x) = o # usevoid x
end;;
[%%expect{|
Line 4, characters 32-33:
4 |   let foo o (A x) = o # usevoid x
                                    ^
Error: This expression has type ('a : void)
       but an expression was expected of type ('b : value)
       'a has layout value, which does not overlap with void.
|}];;

module M10_4 = struct
  val x : < l : t_void >
end;;
[%%expect{|
Line 2, characters 12-22:
2 |   val x : < l : t_void >
                ^^^^^^^^^^
Error: Object field types must have layout value.
        t_void has layout void, which is not a sublayout of value.
|}];;

module M10_5 = struct
  type 'a t = < l : 'a s >
  and ('a : void) s = 'a
end;;
[%%expect{|
Line 3, characters 2-24:
3 |   and ('a : void) s = 'a
      ^^^^^^^^^^^^^^^^^^^^^^
Error:
       'a s has layout void, which does not overlap with value.
|}];;

module M10_6 = struct
  type 'a t = < l : 'a > constraint 'a = t_void
end;;
[%%expect{|
Line 2, characters 36-47:
2 |   type 'a t = < l : 'a > constraint 'a = t_void
                                        ^^^^^^^^^^^
Error: The type constraints are not consistent.
       Type ('a : value) is not compatible with type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

(*******************************************************************)
(* Test 11: class parameters and bound vars must have layout value *)

(* Hits `Pcl_let` *)
module M11_1 = struct
  class foo11 v =
    let VV v = v in
    object
      val bar = VV v
    end;;
end
[%%expect{|
Line 3, characters 11-12:
3 |     let VV v = v in
               ^
Error: Variables bound in a class must have layout value.
       v has layout void, which is not a sublayout of value.
|}];;

(* Hits the Cfk_concrete case of Pcf_val *)
module M11_2 = struct
  class foo v =
    object
      val bar = v.vr_void
    end
end;;
[%%expect{|
Line 4, characters 10-13:
4 |       val bar = v.vr_void
              ^^^
Error: Variables bound in a class must have layout value.
       bar has layout void, which is not a sublayout of value.
|}];;

(* Hits the Cfk_virtual case of Pcf_val *)
module M11_3 = struct
  class virtual foo =
    object
      val virtual bar : t_void
    end
end;;
[%%expect{|
Line 4, characters 18-21:
4 |       val virtual bar : t_void
                      ^^^
Error: Variables bound in a class must have layout value.
       bar has layout void, which is not a sublayout of value.
|}];;

module M11_4 = struct
  type ('a : void) t

  class virtual ['a] foo =
    object
      val virtual baz : 'a t
    end
end
[%%expect{|
Line 6, characters 24-26:
6 |       val virtual baz : 'a t
                            ^^
Error: This type ('a : void) should be an instance of type ('a0 : value)
       'a has layout value, which does not overlap with void.
|}];;

module M11_5 = struct
  type ('a : void) t = A of 'a

  class ['a] foo =
    object
      method void_id (A a) : 'a t = a
    end
end;;
[%%expect{|
Line 6, characters 29-31:
6 |       method void_id (A a) : 'a t = a
                                 ^^
Error: This type ('a : void) should be an instance of type ('a0 : value)
       'a has layout value, which does not overlap with void.
|}];;

module type S11_6 = sig
  type ('a : void) t = A of 'a

  class ['a] foo :
    'a t ->
    object
      method baz : int
    end
end;;
[%%expect{|
Line 5, characters 4-6:
5 |     'a t ->
        ^^
Error: This type ('a : void) should be an instance of type ('a0 : value)
       'a has layout value, which does not overlap with void.
|}];;

module type S11_7 = sig
  class foo :
    object
      val baz : t_void
    end
end;;
[%%expect{|
Line 4, characters 6-22:
4 |       val baz : t_void
          ^^^^^^^^^^^^^^^^
Error: Variables bound in a class must have layout value.
       baz has layout void, which is not a sublayout of value.
|}];;


(***********************************************************)
(* Test 12: built-in type constructors work only on values *)

(* lazy *)
type t12 = t_void Lazy.t;;
[%%expect{|
Line 1, characters 11-17:
1 | type t12 = t_void Lazy.t;;
               ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 (VV v) = lazy v;;
[%%expect{|
Line 1, characters 22-23:
1 | let x12 (VV v) = lazy v;;
                          ^
Error: This expression has type t_void but an expression was expected of type
         ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 v =
  match v with
  | lazy v -> VV v
[%%expect{|
Line 3, characters 17-18:
3 |   | lazy v -> VV v
                     ^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

(* option *)
(* CR layouts v5: allow this *)
type t12 = t_void option;;
[%%expect{|
Line 1, characters 11-17:
1 | type t12 = t_void option;;
               ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 (VV v) = Some v;;
[%%expect{|
Line 1, characters 22-23:
1 | let x12 (VV v) = Some v;;
                          ^
Error: This expression has type t_void but an expression was expected of type
         ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 v =
  match v with
  | Some v -> VV v
  | None -> assert false
[%%expect{|
Line 3, characters 17-18:
3 |   | Some v -> VV v
                     ^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

(* list *)
(* CR layouts: should work after relaxing the mixed block restriction. *)
type t12 = t_void list;;
[%%expect{|
Line 1, characters 11-17:
1 | type t12 = t_void list;;
               ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 (VV v) = [v];;
[%%expect{|
Line 1, characters 18-19:
1 | let x12 (VV v) = [v];;
                      ^
Error: This expression has type t_void but an expression was expected of type
         ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 v =
  match v with
  | [v] -> VV v
  | _ -> assert false
[%%expect{|
Line 3, characters 14-15:
3 |   | [v] -> VV v
                  ^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

(* array *)
(* CR layouts v4: should work *)
type t12 = t_void array;;
[%%expect{|
Line 1, characters 11-17:
1 | type t12 = t_void array;;
               ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 (VV v) = [| v |];;
[%%expect{|
Line 1, characters 20-21:
1 | let x12 (VV v) = [| v |];;
                        ^
Error: This expression has type t_void but an expression was expected of type
         ('a : value)
       t_void has layout void, which is not a sublayout of value.
|}];;

let x12 v =
  match v with
  | [| v |] -> VV v
  | _ -> assert false
[%%expect{|
Line 3, characters 18-19:
3 |   | [| v |] -> VV v
                      ^
Error: This expression has type ('a : value)
       but an expression was expected of type t_void
       t_void has layout void, which is not a sublayout of value.
|}];;

(* Test 13: Examples motivating the trick with the manifest in [enter_type] *)
type t13 = foo13 list
and foo13 = string;;
[%%expect{|
type t13 = foo13 list
and foo13 = string
|}];;

type t13 = foo13 list
and foo13 = t_void;;
[%%expect{|
Line 2, characters 0-18:
2 | and foo13 = t_void;;
    ^^^^^^^^^^^^^^^^^^
Error:
       foo13 has layout void, which is not a sublayout of value.
|}];;

(* Test 14: Type aliases need not have layout value *)
(* (In [transl_type_aux], this hits the layout given to the type variable in the
   Not_found case of the Ptyp_alias case. *)
type ('a : void) t14
type ('a, 'b) foo14 = ('a as 'b) t14 -> 'b t14;;
[%%expect{|
type 'a t14
type ('a, 'b) foo14 = 'a t14 -> 'a t14 constraint 'b = 'a
|}]

(* Test 15: seperability: [msig_of_external_type] logic *)
type 'a t_void_15 [@@void]

type t_15 = T_15 : 'a t_void_15 -> t_15 [@@unboxed];;
[%%expect{|
type 'a t_void_15 [@@void]
type t_15 = T_15 : 'a t_void_15 -> t_15 [@@unboxed]
|}];;

(* Test 16: incremental layout checking of @@unboxed types - see comment on
   [constrain_type_layout]. *)

type 'a t16 = 'a list
type s16 = { lbl : s16 t16 } [@@unboxed];;

[%%expect{|
type 'a t16 = 'a list
type s16 = { lbl : s16 t16; } [@@unboxed]
|}];;

(* Test 17: expansion in [check_univars] *)
(* This test isn't really layouts-specific, but it checks that the layout checks
   we've added in [Typecore.check_univars] don't choke when expansion is needed
   to see a variable *)
type 'a t17 = 'a

let id17 (x : 'a t17) = x

let f17 : 'a . 'a -> 'a = fun x -> id17 x;;

[%%expect{|
type 'a t17 = 'a
val id17 : 'a t17 -> 'a t17 = <fun>
val f17 : 'a -> 'a = <fun>
|}];;

(* Test 18: non-value coercions *)
let f18 () =
  let x : t_void = assert false in
  let _y = (x :> t_void) in
  ();;
[%%expect{|
val f18 : unit -> unit = <fun>
|}];;

(* Test 19: Non-value bodies for let module *)
let f19 () =
  let x : t_void = assert false in
  let _y =
    let module M = struct end in
    x
  in
  ();;
[%%expect{|
val f19 : unit -> unit = <fun>
|}];;

(* Test 20: Non-value unpack body *)
module type M20 = sig end

let f20 () =
  let x : t_void = assert false in
  let _y =
    let (module M) = (module struct end : M20) in
    x
  in
  ();;
[%%expect{|
module type M20 = sig end
val f20 : unit -> unit = <fun>
|}];;


(* CR ccasinghino: Once we allow non-value top-level module definitions, add
   tests showing that things get defaulted to value.

   (CJC XXX actually, once we can annotate universally quantified variables,
   that's probably enough)
*)
