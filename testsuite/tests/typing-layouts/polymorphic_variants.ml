module type S = sig
  type t = [ `Bar of int ]
  val x : int -> t
  val y : [ `Baz of int list ] -> t
end
