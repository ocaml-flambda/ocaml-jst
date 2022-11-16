(* TEST
   * expect
*)

(*
type t_any : any
type t_value : value
type t_imm : immediate
type t_imm64 : immediate64
type t_void : void
;;
[%%expect{|
type t_any : any
type t_value : value
type t_imm : immediate
type t_imm64 : immediate64
type t_void : void
|}];;
*)
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
(*
type ('a : immediate) t2_imm
type t = int t2_any
type t = bool t2_any
;;
[%%expect {|
  ??
|}]

type t = string t2_imm
;;
[%%expect {|
fail
|}]

let f : 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
??
|}]

let f : ('a : immediate) t2_imm -> ('a : value) t2_imm = fun x -> x
;;
[%%expect {|
??
|}]

let f : ('a : value) t2_imm -> ('a : value) t2_imm = fun x -> x
;;
[%%expect {|
??
|}]

let f : ('a : immediate). 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
??
|}]

let f : ('a : value). 'a t2_imm -> 'a t2_imm = fun x -> x
;;
[%%expect {|
fail
|}]

type 'a t = 'a t2_imm
;;
[%%expect {|
??
|}]

type ('a : value) t = 'a t2_imm
;;
[%%expect {|
??
|}]

type ('a : immediate) t = 'a t2_imm
;;
[%%expect {|
??
|}]

let f : ('a : any) -> 'a = fun x -> x
;;
[%%expect {|
??
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
??
|}]

let f { field } = field "hello"
;;
[%%expect {|
fail
|}]

let r = { field = fun x -> x }
let r = { field = Fun.id }
;;
[%%expect {|
??
|}]

let r = { field = fun (type (a : immediate)) (x : a) -> x }
;;
[%%expect {|
??
|}]

let r = { field = fun (type (a : value)) (x : a) -> x }
;;
[%%expect {|
??
|}]

let f = fun (type (a : value)) (x : a) -> x
;;
[%%expect {|
??
|}]

let f = fun (type (a : immediate)) (x : a) -> x
;;
[%%expect {|
??
|}]

let f = fun (type (a : any)) (x : a) -> x
;;
[%%expect {|
fail
|}]

let f : type (a : value). a -> a = fun x -> x
;;
[%%expect {|
??
|}]

let f : type (a : immediate). a -> a = fun x -> x
;;
[%%expect {|
??
|}]

let f : type (a : any). a -> a = fun x -> x
;;
[%%expect {|
fail
|}]
*)
