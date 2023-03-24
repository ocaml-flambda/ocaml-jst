(* TEST
   * skip
   reason = "unboxed types aren't implemented yet"
   ** expect
*)
(* CR layouts (v2): enable this test *)

(* annoyingly, we must write out the module signature separately for
   each unboxed int, because we don't have abstract layouts. *)
(* CR layouts (v10): Use one signature, specialized *)

module type Uint64 = sig
  val (+) : #int64 -> #int64 -> #int64
  val (-) : #int64 -> #int64 -> #int64
  val ( * ) : #int64 -> #int64 -> #int64
  val (/) : #int64 -> #int64 -> #int64
  val (mod) : #int64 -> #int64 -> #int64

  val ( ~- ) : #int64 -> #int64

  val zero : #int64
  val one : #int64
  val minus_one : #int64
  val neg : #int64 -> #int64
  val add : #int64 -> #int64 -> #int64
  val sub : #int64 -> #int64 -> #int64
  val mul : #int64 -> #int64 -> #int64
  val div : #int64 -> #int64 -> #int64
  val unsigned_div : #int64 -> #int64 -> #int64
  val rem : #int64 -> #int64 -> #int64
  val unsigned_rem : #int64 -> #int64 -> #int64
  val succ : #int64 -> #int64
  val pred : #int64 -> #int64
  val abs : #int64 -> #int64
  val max_int : #int64
  val min_int : #int64
  val logand : #int64 -> #int64 -> #int64
  val logor : #int64 -> #int64 -> #int64
  val logxor : #int64 -> #int64 -> #int64
  val lognot : #int64 -> #int64
  val shift_left : #int64 -> int -> #int64
  val shift_right : #int64 -> int -> #int64
  val shift_right_logical : #int64 -> int -> #int64
  val of_int : int -> #int64
  val to_int : #int64 -> int
  val unsigned_to_int : #int64 -> int or_null (* CR layouts (v3): add this line *)
  val of_int64 : int64 -> #int64
  val to_int64 : #int64 -> int64
  val of_float : float -> #int64
  val of_ufloat : #float -> #int64
  val to_float : #int64 -> float
  val to_ufloat : #int64 -> #float
  val of_uint32 : #int32 -> #int64
  val to_uint32 : #int64 -> #int32
  val of_unativeint : #nativeint -> #int64
  val to_unativeint : #int64 -> #nativeint
  val of_string : string -> #int64
  val of_string_opt : string -> #int64 option (* CR layouts (v5): add this line *)
  val to_string : #int64 -> string
  val bits_of_float : float -> #int64
  val bits_of_ufloat : #float -> #int64
  val float_of_bits : #int64 -> float
  val ufloat_of_bits : #int64 -> #float

  type t = #int64
  val compare : t -> t -> int
  val unsigned_compare : t -> t -> int
  val equal : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
end

module Uint64 : Uint64 = Uint64

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


module type Unativeint = sig
  val (+) : #nativeint -> #nativeint -> #nativeint
  val (-) : #nativeint -> #nativeint -> #nativeint
  val ( * ) : #nativeint -> #nativeint -> #nativeint
  val (/) : #nativeint -> #nativeint -> #nativeint
  val (mod) : #nativeint -> #nativeint -> #nativeint

  val ( ~- ) : #nativeint -> #nativeint

  val zero : #nativeint
  val one : #nativeint
  val minus_one : #nativeint
  val neg : #nativeint -> #nativeint
  val add : #nativeint -> #nativeint -> #nativeint
  val sub : #nativeint -> #nativeint -> #nativeint
  val mul : #nativeint -> #nativeint -> #nativeint
  val div : #nativeint -> #nativeint -> #nativeint
  val unsigned_div : #nativeint -> #nativeint -> #nativeint
  val rem : #nativeint -> #nativeint -> #nativeint
  val unsigned_rem : #nativeint -> #nativeint -> #nativeint
  val succ : #nativeint -> #nativeint
  val pred : #nativeint -> #nativeint
  val abs : #nativeint -> #nativeint
  val max_int : #nativeint
  val min_int : #nativeint
  val logand : #nativeint -> #nativeint -> #nativeint
  val logor : #nativeint -> #nativeint -> #nativeint
  val logxor : #nativeint -> #nativeint -> #nativeint
  val lognot : #nativeint -> #nativeint
  val shift_left : #nativeint -> int -> #nativeint
  val shift_right : #nativeint -> int -> #nativeint
  val shift_right_logical : #nativeint -> int -> #nativeint
  val of_int : int -> #nativeint
  val to_int : #nativeint -> int
  val unsigned_to_int : #nativeint -> int or_null (* CR layouts (v3): add this line *)
  val of_nativeint : nativeint -> #nativeint
  val to_nativeint : #nativeint -> nativeint
  val of_float : float -> #nativeint
  val of_ufloat : #float -> #nativeint
  val to_float : #nativeint -> float
  val to_ufloat : #nativeint -> #float
  val of_uint64 : #int64 -> #nativeint
  val to_uint64 : #nativeint -> #int64
  val of_uint32 : #int32 -> #nativeint
  val to_uint32 : #nativeint -> #int32
  val of_string : string -> #nativeint
  val of_string_opt : string -> #nativeint option (* CR layouts (v5): add this line *)
  val to_string : #nativeint -> string
  val bits_of_float : float -> #nativeint
  val bits_of_ufloat : #float -> #nativeint
  val float_of_bits : #nativeint -> float
  val ufloat_of_bits : #nativeint -> #float

  type t = #nativeint
  val compare : t -> t -> int
  val unsigned_compare : t -> t -> int
  val equal : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
end

module Unativeint : Unativeint = Unativeint

[%%expect {|
success
|}]

let x = #3L
let x = #3l
let x = #3n

[%%expect {|
success
|}]

let x = Uint64.(#3L + #4L)
let x = Uint32.(#3l + #4l)
let x = Unativeint.(#3n + #4n)

[%%expect {|
success
|}]

(* wrong + *)
let bad = #3L + #4L
let bad = #3l + #4l
let bad = #3n + #4n

[%%expect {|
error
|}]

let bad = Uint64.(#3L+#4L)  (* doesn't parse correctly *)

[%%expect {|
error
|}]

let bad = #3

[%%expect {|
parse error
|}]

(* CR layouts (v5): replace [unit] with [#unit] *)
module type Random = sig
  val init : int -> unit

  val uint32 : #int32 -> #int32
  val ubits32 : unit -> #int32

  val unativeint : #nativeint -> #nativeint
  val unativebits : unit -> #nativeint

  val uint64 : #int64 -> #int64
  val ubits64 : unit -> #int64

  val ufloat : #float -> #float
end

module Random : Random = Random

[%%expect {|
success
|}]
