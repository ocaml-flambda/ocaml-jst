(* TEST
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
*)
(* CR layouts (v2): enable this test *)

module type S = sig
  type t : any
  val f : unit -> t -> t
end

[%%expect {|
success
|}]

module M (X : sig type t end) : S with type t = X.t = struct
  type t = X.t
  let f _ x = x
end

[%%expect {|
success
|}]


module M_any : S = struct
  type t : any
  let rec f _ = f ()
end

[%%expect {|
success
|}]

module M2 = struct
  let mk_void : unit -> ('a : void) = assert false
  let mk_imm : unit -> ('a : immediate) = assert false

  let x1 () = M_any.f () (mk_void ())
  let x2 () = M_any.f () (mk_imm ())
end

[%%expect {|
success
|}]

module M3 (X : sig val x : M_any.t end) = struct
  let blah = M_any.f () X.x
end

[%%expect {|
error
|}]
