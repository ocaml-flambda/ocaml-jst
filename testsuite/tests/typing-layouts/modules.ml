(* TEST
   * expect
*)

type t_any   [@@any]
type t_value [@@value]
type t_imm   [@@immediate]
type t_imm64 [@@immediate64]
type t_void  [@@void];;


(* Test 1: Simple with type constraints respect layouts. *)
module type S1 = sig
  type 'a [@void] t
  type s
end;;

type 'a [@void] t1;;

module type S1' = S1 with type 'a t = t_void t1 and type s = t_void t1;;
[%%expect {|
type t_any [@@any]
type t_value [@@value]
type t_imm [@@immediate]
type t_imm64 [@@immediate64]
type t_void [@@void]
module type S1 = sig type 'a t type s end
type 'a t1
module type S1' = sig type 'a t = t_void t1 type s = t_void t1 end
|}];;

module type S1'' = S1 with type 'a t = 'a list;;
[%%expect {|
Line 1, characters 32-34:
1 | module type S1'' = S1 with type 'a t = 'a list;;
                                    ^^
Error: The type constraints are not consistent.
Type 'a is not compatible with type 'b
'a has layout void, which does not overlap with value.
|}];;
(* CJC XXX error message *)

module type S1'' = S1 with type s = t_void;;

[%%expect{|
Line 1, characters 27-42:
1 | module type S1'' = S1 with type s = t_void;;
                               ^^^^^^^^^^^^^^^
Error: This type has layout void, which is not a sublayout of value.
|}]

(* Test 2: with type constraints for fixed types (the complicated case of
   Type_mod.merge_constraint) *)
module type S2 = sig
  type 'a [@void] t
end

type 'a [@void] r2 = R
type 'a [@void] s2 = private [> `A of 'a r2]

module type T2 = S2 with type 'a t = 'a s2

module F2 (X : T2) = struct
  let f () : 'a X.t = `A R
end;;
[%%expect{|
module type S2 = sig type 'a t end
type 'a r2 = R
type !'a s2 = private [> `A of 'a r2 ]
module type T2 = sig type 'a t = 'a s2 end
module F2 : functor (X : T2) -> sig val f : unit -> 'a X.t end
|}]

type 'a [@void] s2' = private [> `B of 'a]
module type T2' = S2 with type 'a t = 'a s2'

module F2' (X : T2') = struct
  let f () : 'a X.t = `B 3
end
[%%expect{|
type !'a s2' = private [> `B of 'a ]
module type T2' = sig type 'a t = 'a s2' end
Line 5, characters 25-26:
5 |   let f () : 'a X.t = `B 3
                             ^
Error: This expression has type int but an expression was expected of type 'a
       int has layout immediate, which is not a sublayout of void.
|}]

type 'a [@void] s2' = private [> `B of 'a]
module type T2' = S2 with type 'a t = 'a list;;
[%%expect{|
type !'a s2' = private [> `B of 'a ]
Line 2, characters 31-33:
2 | module type T2' = S2 with type 'a t = 'a list;;
                                   ^^
Error: The type constraints are not consistent.
Type 'a is not compatible with type 'b
'a has layout void, which does not overlap with value.
|}]

(* Test 3: Recursive modules, with and without layout annotations *)
module rec Foo3 : sig
  val create : Bar3.t -> unit
end = struct
  let create _ = ()
end

and Bar3 : sig
  type t
end = struct
  type t = unit
end;;
[%%expect {|
module rec Foo3 : sig val create : Bar3.t -> unit end
and Bar3 : sig type t end
|}];;

module rec Foo3 : sig
  val create : Bar3.t -> unit
end = struct
  let create _ = ()
end

and Bar3 : sig
  type t [@@void]
end = struct
  type t
end;;
[%%expect {|
Line 2, characters 15-21:
2 |   val create : Bar3.t -> unit
                   ^^^^^^
Error: Function argument types must have layout value.
        Bar3.t has layout void, which is not a sublayout of value.
|}];;

module rec Foo3 : sig
  type t = Bar3.t [@@immediate]
end = struct
  type t = Bar3.t
end

and Bar3 : sig
  type t [@@value]
end = struct
  type t = A
end;;
[%%expect {|
Line 2, characters 2-31:
2 |   type t = Bar3.t [@@immediate]
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This type has layout value, which is not a sublayout of immediate.
|}];;

module rec Foo3 : sig
  type t = Bar3.t [@@immediate]
end = struct
  type t = Bar3.t
end

and Bar3 : sig
  type t [@@immediate]
end = struct
  type t = A
end;;
[%%expect {|
module rec Foo3 : sig type t = Bar3/2.t [@@immediate] end
and Bar3 : sig type t [@@immediate] end
|}];;

module rec Foo3 : sig
  type 'a t = 'a Bar3.t * 'a list
end = struct
  type t = 'a Bar3.t * 'a list
end

and Bar3 : sig
  type 'a [@void] t
end = struct
  type 'a t
end;;
[%%expect {|
Line 2, characters 26-28:
2 |   type 'a t = 'a Bar3.t * 'a list
                              ^^
Error: This type 'a should be an instance of type 'b
       'a has layout void, which does not overlap with value.
|}];;
(* CJC XXX bad error message *)


(* One downside of the current approach - this could be allowed, but isn't.  You
   need to annotate types declared in recursive modules if they need to have
   layouts other than value, even if it's obvious from the manifest *)
type t3 [@@void]

module rec Foo3 : sig
  type t = t3
end = struct
  type t = t3
end

and Bar3 : sig
  type 'a [@void] t

  type s = Foo3.t t
end = struct
  type 'a [@void] t
  type s = Foo3.t t
end;;
[%%expect {|
type t3 [@@void]
Line 12, characters 11-17:
12 |   type s = Foo3.t t
                ^^^^^^
Error: This type Foo3.t should be an instance of type 'a
       Foo3.t has layout value, which is not a sublayout of void.
|}];;

(* Previous example works with annotation *)
module rec Foo3 : sig
  type t = t3 [@@void]
end = struct
  type t = t3
end

and Bar3 : sig
  type 'a [@void] t

  type s = Foo3.t t
end = struct
  type 'a [@void] t
  type s = Foo3.t t
end;;
[%%expect {|
module rec Foo3 : sig type t = t3 [@@void] end
and Bar3 : sig type 'a t type s = Foo3/2.t t end
|}];;
