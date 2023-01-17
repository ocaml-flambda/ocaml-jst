(* TEST
   * expect
*)

(* XXX layouts: merge this with annots.ml after these all pass *)

class c : object
  val f : 'a -> 'a
end = object
  val f = fun (x : ('a : immediate)) -> x
end
;;
[%%expect {|
fail
|}]

type ('a : immediate) t2_imm

type s = { f : ('a : value) . 'a -> 'a u }
and 'a u = 'a t2_imm

[%%expect {|
fail
|}]

class c : object
  method m : ('a : immediate). 'a -> 'a
  val f : ('a : immediate) -> 'a
end = object
  method m : type (a : immediate). a -> a = fun x -> x
  val f = fun (x : ('a : immediate)) -> x
end

[%%expect {|
class c : object method m : 'a -> 'a end BAD
|}]

type _ g = | MkG : ('a : immediate) ('b : void). 'a -> 'b g

type ('a : void) t3 = ..
type _ t3 += MkG : ('a : immediate) 'b. 'a -> 'b t3

[%%expect {|
success (I think)
|}]

let f_gadt : ('a : value). 'a -> 'a g -> 'a = fun x MkG -> f_imm x

[%%expect {|
success
|}]
