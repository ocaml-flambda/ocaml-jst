(* TEST
   * expect
*)


type t_any : any
type t_value : value
type t_imm : immediate
type t_imm64 : immediate64
type t_void : void
;;
[%%expect{|
type t_any : any
type t_value
type t_imm : immediate
type t_imm64 : immediate64
type t_void : void
|}];;

let x : (int : value) = 5
let x : (int : immediate) = 5
let x : (int : any) = 5
;;
[%%expect {|
val x : int = 5
val x : int = 5
val x : int = 5
|}]

let x : ((int : immediate) list : value) = [3;4;5]
;;
[%%expect {|
val x : int list = [3; 4; 5]
|}]

let x : (int list : immediate) = [3;4;5]
;;
[%%expect {|
Line 1, characters 8-30:
1 | let x : (int list : immediate) = [3;4;5]
            ^^^^^^^^^^^^^^^^^^^^^^
Error: Bad layout annotation:
         int list has layout value, which is not a sublayout of immediate.
|}]

type ('a : immediate) t2_imm
type t = int t2_imm
type t = bool t2_imm
;;
[%%expect {|
type ('a : immediate) t2_imm
type t = int t2_imm
type t = bool t2_imm
|}]

type t = string t2_imm
;;
[%%expect {|
Line 1, characters 9-15:
1 | type t = string t2_imm
             ^^^^^^
Error: This type string should be an instance of type 'a
       string has layout value, which is not a sublayout of immediate.
|}]

let f : 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
val f : ('a : immediate). 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : immediate) t2_imm -> ('a : value) t2_imm = fun x -> x
;;
[%%expect {|
val f : ('a : immediate). 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : value) t2_imm -> ('a : value) t2_imm = fun x -> x
;;
[%%expect {|
val f : ('a : immediate). 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : immediate). 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
val f : ('a : immediate). 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : value). 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
Line 1, characters 8-44:
1 | let f : ('a : value). 'a t2_imm -> 'a t2_imm = fun x -> x
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The universal type variable 'a was declared to have
       layout value, but was inferred to have layout immediate.
|}]

type 'a t = 'a t2_imm
;;
[%%expect {|
type ('a : immediate) t = 'a t2_imm
|}]

type ('a : value) t = 'a t2_imm
;;
[%%expect {|
type ('a : immediate) t = 'a t2_imm
|}]

type ('a : immediate) t = 'a t2_imm
;;
[%%expect {|
type ('a : immediate) t = 'a t2_imm
|}]

let f : ('a : any) -> 'a = fun x -> x
;;
[%%expect {|
val f : 'a -> 'a = <fun>
|}]

let f : ('a : any). 'a -> 'a = fun x -> x
;;
[%%expect {|
Line 1, characters 8-28:
1 | let f : ('a : any). 'a -> 'a = fun x -> x
            ^^^^^^^^^^^^^^^^^^^^
Error: The universal type variable 'a was declared to have
       layout any, but was inferred to have layout value.
|}]
(* CR layouts (v2): This error message should change to complain
   about the [fun x], not the arrow type. *)

type r = { field : ('a : immediate). 'a -> 'a }
let f { field } = field 5
;;
[%%expect {|
type r = { field : ('a : immediate). 'a -> 'a; }
val f : r -> int = <fun>
|}]

let f { field } = field "hello"
;;
[%%expect {|
Line 1, characters 24-31:
1 | let f { field } = field "hello"
                            ^^^^^^^
Error: This expression has type string but an expression was expected of type
         'a
       string has layout value, which is not a sublayout of immediate.
|}]

let r = { field = fun x -> x }
let r = { field = Fun.id }
;;
[%%expect {|
val r : r = {field = <fun>}
val r : r = {field = <fun>}
|}]

let r = { field = fun (type (a : immediate)) (x : a) -> x }
;;
[%%expect {|
val r : r = {field = <fun>}
|}]

let r = { field = fun (type (a : value)) (x : a) -> x }
;;
[%%expect {|
val r : r = {field = <fun>}
|}]

let f = fun (type (a : value)) (x : a) -> x
;;
[%%expect {|
val f : 'a -> 'a = <fun>
|}]

let f = fun (type (a : immediate)) (x : a) -> x
;;
[%%expect {|
val f : ('a : immediate). 'a -> 'a = <fun>
|}]

let f = fun (type (a : any)) (x : a) -> x
;;
[%%expect {|
Line 1, characters 29-36:
1 | let f = fun (type (a : any)) (x : a) -> x
                                 ^^^^^^^
Error: This pattern matches values of type a
       but a pattern was expected which matches values of type 'a
       a has layout any, which is not a sublayout of value.
|}]

let f : type (a : value). a -> a = fun x -> x
;;
[%%expect {|
val f : 'a -> 'a = <fun>
|}]

let f : type (a : immediate). a -> a = fun x -> x
;;
[%%expect {|
val f : ('a : immediate). 'a -> 'a = <fun>
|}]

let f : type (a : any). a -> a = fun x -> x
;;
[%%expect {|
Line 1, characters 4-43:
1 | let f : type (a : any). a -> a = fun x -> x
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The universal type variable 'a was declared to have
       layout any, but was inferred to have layout value.
|}]
(* CR layouts (v2): This error message will change to complain
   about the fun x, not the arrow type. *)

module type S = sig
  val f : 'a. 'a t2_imm -> 'a t2_imm
end
;;
[%%expect {|
Line 2, characters 10-36:
2 |   val f : 'a. 'a t2_imm -> 'a t2_imm
              ^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The universal type variable 'a was defaulted to have
       layout value, but was inferred to have layout immediate.
|}]

module type S = sig
  val f : ('a : value). 'a t2_imm -> 'a t2_imm
end
;;
[%%expect {|
Line 2, characters 10-46:
2 |   val f : ('a : value). 'a t2_imm -> 'a t2_imm
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The universal type variable 'a was declared to have
       layout value, but was inferred to have layout immediate.
|}]

module type S = sig
  val f : 'a t2_imm -> 'a t2_imm
  val g : ('a : immediate). 'a t2_imm -> 'a t2_imm
end
;;
[%%expect {|
module type S =
  sig
    val f : ('a : immediate). 'a t2_imm -> 'a t2_imm
    val g : ('a : immediate). 'a t2_imm -> 'a t2_imm
  end
|}]

let f (x : ('a : immediate). 'a -> 'a) = x "string"

[%%expect {|
Line 1, characters 43-51:
1 | let f (x : ('a : immediate). 'a -> 'a) = x "string"
                                               ^^^^^^^^
Error: This expression has type string but an expression was expected of type
         'a
       string has layout value, which is not a sublayout of immediate.
|}]

class c : object
  val f : 'a -> 'a
end = object
  val f = fun (x : ('a : immediate)) -> x
end
;;
[%%expect {|
fail
|}]

type s = { f : ('a : value) . 'a -> 'a u }
and 'a u = 'a t2_imm

[%%expect {|
fail
|}]

(* and now, some parsing & printing tests. *)

let f (type a : immediate) (x : a) = x
let f = fun (type a : immediate) (x : a) -> x
let f = fun (type a : value) (x : a) -> x

class c : object
  method m : ('a : immediate). 'a -> 'a
  val f : ('a : immediate) -> 'a
end = object
  method m : type (a : immediate). a -> a = fun x -> x
  val f = fun (x : ('a : immediate)) -> x
end

let o = object
  method m : type (a : immediate). a -> a = fun x -> x
end

let f : type (a : immediate). a -> a = fun x -> x
let f x =
  let local_ g (type a : immediate) (x : a) = x in
  g x [@nontail]
let f = fun x y (type (a : immediate)) (z : a) -> z
let f = fun x y (type a : immediate) (z : a) -> z

external f : ('a : immediate). 'a -> 'a = "%identity"

type (_ : void) t2_void
exception E : ('a : immediate) ('b : void). 'b t2_void * 'a list -> exn

let f (x : ('a : immediate). 'a -> 'a) = x 3, x true

[%%expect {|
val f : ('a : immediate). 'a -> 'a = <fun>
val f : ('a : immediate). 'a -> 'a = <fun>
val f : 'a -> 'a = <fun>
class c : object method m : 'a -> 'a end BAD
val o : < m : ('a : immediate). 'a -> 'a > = <obj>
val f : ('a : immediate). 'a -> 'a = <fun>
val f : ('a : immediate). 'a -> 'a = <fun>
val f : ('a : immediate) 'c 'b. 'b -> 'c -> 'a -> 'a = <fun>
val f : ('a : immediate) 'c 'b. 'b -> 'c -> 'a -> 'a = <fun>
external f : ('a : immediate). 'a -> 'a = "%identity"
type (_ : void) t2_void
exception E : ('a : immediate) ('b : void). 'b t2_void * 'a list -> exn
val f : (('a : immediate). 'a -> 'a) -> int * bool = <fun>
|}]

type _ a = Mk : [> ] * ('a : immediate) -> int a

[%%expect {|
type _ a = Mk : ('a : immediate). [>  ] * 'a -> int a
|}]

type _ g = | MkG : ('a : immediate) ('b : void). 'a -> 'b g

type ('a : void) t3 = ..
type _ t3 += MkG : ('a : immediate) 'b. 'a -> 'b t3

[%%expect {|
success (I think)
|}]

let f_imm : ('a : immediate). 'a -> 'a = fun x -> x

[%%expect {|
val f_imm : ('a : immediate). 'a -> 'a = <fun>
|}]

let f_val : ('a : value). 'a -> 'a = fun x -> f_imm x

[%%expect {|
Line 1, characters 37-53:
1 | let f_val : ('a : value). 'a -> 'a = fun x -> f_imm x
                                         ^^^^^^^^^^^^^^^^
Error: This definition has type 'b -> 'b which is less general than
         'a. 'a -> 'a
       'a has layout value, which is not a sublayout of immediate.
|}]

type (_ : value) g =
  | MkG : ('a : immediate). 'a g

[%%expect {|
type _ g = MkG : ('a : immediate). 'a g
|}]

let f_gadt : ('a : value). 'a -> 'a g -> 'a = fun x MkG -> f_imm x

[%%expect {|
success
|}]
