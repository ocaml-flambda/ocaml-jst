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
val f : 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : immediate) t2_imm -> ('a : value) t2_imm = fun x -> x
;;
[%%expect {|
val f : 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : value) t2_imm -> ('a : value) t2_imm = fun x -> x
;;
[%%expect {|
val f : 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : immediate). 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
val f : 'a t2_imm -> 'a t2_imm = <fun>
|}]

let f : ('a : value). 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
fail
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
fail
|}]

type r = { field : ('a : immediate). 'a -> 'a }
let f { field } = field 5
;;
[%%expect {|
type r = { field : 'a. 'a -> 'a; }
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
fail?? needs a coercion??
|}]

let f = fun (type (a : value)) (x : a) -> x
;;
[%%expect {|
val f : 'a -> 'a = <fun>
|}]

let f = fun (type (a : immediate)) (x : a) -> x
;;
[%%expect {|
??
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
??
|}]

let f : type (a : any). a -> a = fun x -> x
;;
[%%expect {|
Line 1, characters 24-25:
1 | let f : type (a : any). a -> a = fun x -> x
                            ^
Error: Function argument types must have layout value.
        a has layout any, which is not a sublayout of value.
|}]

module type S = sig
  val f : 'a. 'a t2_imm -> 'a t2_imm
end
;;
[%%expect {|
fail
|}]

module type S = sig
  val f : ('a : value). 'a t2_imm -> 'a t2_imm
end
;;
[%%expect {|
fail
|}]

module type S = sig
  val f : 'a t2_imm -> 'a t2_imm
  val g : ('a : immediate). 'a t2_imm -> 'a t2_imm
end
;;
[%%expect {|
success
|}]
