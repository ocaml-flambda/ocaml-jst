(* These should both be rejected *)

module type S1 = sig
  type t [@@void]

  val foo : t -> int
end

module type S2 = sig
  type t [@@void]

  val foo : int -> t
end
