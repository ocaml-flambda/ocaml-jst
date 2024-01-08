(* TEST
   * skip
   reason = "unboxed types aren't implemented yet"
   ** expect
*)
(* CR layouts (v4): enable this test *)

(* CR layouts (v10): Use one signature, specialized *)

module type Uint16 = sig
  val (+) : #int16 -> #int16 -> #int16
  val (-) : #int16 -> #int16 -> #int16
  val ( * ) : #int16 -> #int16 -> #int16
  val (/) : #int16 -> #int16 -> #int16
  val (mod) : #int16 -> #int16 -> #int16

  val ( ~- ) : #int16 -> #int16

  val zero : #int16
  val one : #int16
  val minus_one : #int16
  val neg : #int16 -> #int16
  val add : #int16 -> #int16 -> #int16
  val sub : #int16 -> #int16 -> #int16
  val mul : #int16 -> #int16 -> #int16
  val div : #int16 -> #int16 -> #int16
  val unsigned_div : #int16 -> #int16 -> #int16
  val rem : #int16 -> #int16 -> #int16
  val unsigned_rem : #int16 -> #int16 -> #int16
  val succ : #int16 -> #int16
  val pred : #int16 -> #int16
  val abs : #int16 -> #int16
  val max_int : #int16
  val min_int : #int16
  val logand : #int16 -> #int16 -> #int16
  val logor : #int16 -> #int16 -> #int16
  val logxor : #int16 -> #int16 -> #int16
  val lognot : #int16 -> #int16
  val shift_left : #int16 -> int -> #int16
  val shift_right : #int16 -> int -> #int16
  val shift_right_logical : #int16 -> int -> #int16
  val of_int : int -> #int16
  val to_int : #int16 -> int
  val unsigned_to_int : #int16 -> int or_null (* CR layouts (v3): add this line *)
  val of_float : float -> #int16
  val of_ufloat : #float -> #int16
  val to_float : #int16 -> float
  val to_ufloat : #int16 -> #float
  val of_uint32 : #int32 -> #int16
  val to_uint32 : #int16 -> #int32
  val of_uint64 : #int64 -> #int16
  val to_uint64 : #int16 -> #int64
  val of_unativeint : #nativeint -> #int16
  val to_unativeint : #int16 -> #nativeint
  val of_string : string -> #int16
  val of_string_opt : string -> #int16 option (* CR layouts (v5): add this line *)
  val to_string : #int16 -> string

  type t = #int16
  val compare : t -> t -> int
  val unsigned_compare : t -> t -> int
  val equal : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
end

module Uint16 : Uint16 = Uint16

[%%expect {|
success
|}]

module type Uint32 = sig
  val (+) : #int32 -> #int32 -> #int32
  val (-) : #int32 -> #int32 -> #int32
  val ( * ) : #int32 -> #int32 -> #int32
  val (/) : #int32 -> #int32 -> #int32
  val (mod) : #int32 -> #int32 -> #int32

  val ( ~- ) : #int32 -> #int32

  val zero : #int32
  val one : #int32
  val minus_one : #int32
  val neg : #int32 -> #int32
  val add : #int32 -> #int32 -> #int32
  val sub : #int32 -> #int32 -> #int32
  val mul : #int32 -> #int32 -> #int32
  val div : #int32 -> #int32 -> #int32
  val unsigned_div : #int32 -> #int32 -> #int32
  val rem : #int32 -> #int32 -> #int32
  val unsigned_rem : #int32 -> #int32 -> #int32
  val succ : #int32 -> #int32
  val pred : #int32 -> #int32
  val abs : #int32 -> #int32
  val max_int : #int32
  val min_int : #int32
  val logand : #int32 -> #int32 -> #int32
  val logor : #int32 -> #int32 -> #int32
  val logxor : #int32 -> #int32 -> #int32
  val lognot : #int32 -> #int32
  val shift_left : #int32 -> int -> #int32
  val shift_right : #int32 -> int -> #int32
  val shift_right_logical : #int32 -> int -> #int32
  val of_int : int -> #int32
  val to_int : #int32 -> int
  val unsigned_to_int : #int32 -> int or_null (* CR layouts (v3): add this line *)
  val of_int32 : int32 -> #int32
  val to_int32 : #int32 -> int32
  val of_float : float -> #int32
  val of_ufloat : #float -> #int32
  val to_float : #int32 -> float
  val to_ufloat : #int32 -> #float
  val of_uint64 : #int64 -> #int32
  val to_uint64 : #int32 -> #int64
  val of_unativeint : #nativeint -> #int32
  val to_unativeint : #int32 -> #nativeint
  val of_string : string -> #int32
  val of_string_opt : string -> #int32 option (* CR layouts (v5): add this line *)
  val to_string : #int32 -> string
  val bits_of_float : float -> #int32
  val bits_of_ufloat : #float -> #int32
  val float_of_bits : #int32 -> float
  val ufloat_of_bits : #int32 -> #float

  type t = #int32
  val compare : t -> t -> int
  val unsigned_compare : t -> t -> int
  val equal : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
end

module Uint32 : Uint32 = Uint32

[%%expect {|
success
|}]

module type Uint8 = sig
  val (+) : #int8 -> #int8 -> #int8
  val (-) : #int8 -> #int8 -> #int8
  val ( * ) : #int8 -> #int8 -> #int8
  val (/) : #int8 -> #int8 -> #int8
  val (mod) : #int8 -> #int8 -> #int8

  val ( ~- ) : #int8 -> #int8

  val zero : #int8
  val one : #int8
  val minus_one : #int8
  val neg : #int8 -> #int8
  val add : #int8 -> #int8 -> #int8
  val sub : #int8 -> #int8 -> #int8
  val mul : #int8 -> #int8 -> #int8
  val div : #int8 -> #int8 -> #int8
  val unsigned_div : #int8 -> #int8 -> #int8
  val rem : #int8 -> #int8 -> #int8
  val unsigned_rem : #int8 -> #int8 -> #int8
  val succ : #int8 -> #int8
  val pred : #int8 -> #int8
  val abs : #int8 -> #int8
  val max_int : #int8
  val min_int : #int8
  val logand : #int8 -> #int8 -> #int8
  val logor : #int8 -> #int8 -> #int8
  val logxor : #int8 -> #int8 -> #int8
  val lognot : #int8 -> #int8
  val shift_left : #int8 -> int -> #int8
  val shift_right : #int8 -> int -> #int8
  val shift_right_logical : #int8 -> int -> #int8
  val of_int : int -> #int8
  val to_int : #int8 -> int
  val unsigned_to_int : #int8 -> int or_null (* CR layouts (v3): add this line *)
  val of_float : float -> #int8
  val of_ufloat : #float -> #int8
  val to_float : #int8 -> float
  val to_ufloat : #int8 -> #float
  val of_uint32 : #int32 -> #int8
  val to_uint32 : #int8 -> #int32
  val of_uint64 : #int64 -> #int8
  val to_uint64 : #int8 -> #int64
  val of_unativeint : #nativeint -> #int8
  val to_unativeint : #int8 -> #nativeint
  val of_string : string -> #int8
  val of_string_opt : string -> #int8 option (* CR layouts (v5): add this line *)
  val to_string : #int8 -> string

  type t = #int8
  val compare : t -> t -> int
  val unsigned_compare : t -> t -> int
  val equal : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
end

module Uint8 : Uint8 = Uint8

[%%expect {|
success
|}]

let x = #3s
let x = #3b

[%%expect {|
success
|}]

let x = Uint16.(#3s + #4s)
let x = Uint8.(#3b + #4b)

[%%expect {|
success
|}]

let bad = #3s + #4s  (* wrong + *)
let bad = #3b + #4b

[%%expect {|
error
|}]

(* CR layouts (v5): replace [unit] with [#unit] *)
module type Random = sig
  val init : int -> unit

  val uint16 : #int16 -> #int16
  val ubits16 : unit -> #int16

  val uint8 : #int8 -> #int8
  val ubits8 : unit -> #int8
end

module Random : Random = Random

[%%expect {|
success
|}]

(* CR layouts (v4): add quickcheck-style correctness tests
   for the functions above *)
