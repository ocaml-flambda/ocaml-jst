(* TEST
   * expect
*)

(* #float *)

module type Ufloat = sig
  val (+) : #float -> #float -> #float
  val (-) : #float -> #float -> #float
  val ( * ) : #float -> #float -> #float
  val (/) : #float -> #float -> #float
  val ( ** ) : #float -> #float -> #float

  val ( ~- ) : #float -> #float

  val zero : #float
  val one : #float
  val minus_one : #float
  val neg : #float -> #float
  val add : #float -> #float -> #float
  val sub : #float -> #float -> #float
  val mul : #float -> #float -> #float
  val div : #float -> #float -> #float
  val fma : #float -> #float -> #float -> #float
  val rem : #float -> #float -> #float
  val succ : #float -> #float
  val pred : #float -> #float
  val abs : #float -> #float
  val infinity : #float
  val neg_infinity : #float
  val nan : #float
  val pi : #float
  val max_float : #float
  val min_float : #float
  val epsilon : #float
  val is_finite : #float -> bool
  val is_infinite : #float -> bool
  val is_nan : #float -> bool
  val is_integer: #float -> bool
  val of_int : int -> #float
  val to_int : #float -> int
  val of_float : float -> #float
  val to_float : #float -> float
  val of_string : string -> #float
  val of_string_opt : string -> #float option  (* Part of v5 *)
  val to_string : #float -> string

  type fpclass = Float.fpclass =
    | FP_normal
    | FP_subnormal
    | FP_zero
    | FP_infinite
    | FP_nan

  val classify_float : #float -> fpclass
  val pow : #float -> #float -> #float
  val sqrt : #float -> #float
  val cbrt : #float -> #float
  val exp : #float -> #float
  val exp2 : #float -> #float
  val log : #float -> #float
  val log10 : #float -> #float
  val log2 : #float -> #float
  val expm1 : #float -> #float
  val log1p : #float -> #float
  val cos : #float -> #float
  val sin : #float -> #float
  val tan : #float -> #float
  val acos : #float -> #float
  val asin : #float -> #float
  val atan : #float -> #float
  val atan2 : #float -> #float -> #float
  val hypot : #float -> #float -> #float
  val cosh : #float -> #float
  val sinh : #float -> #float
  val tanh : #float -> #float
  val acosh : #float -> #float
  val asinh : #float -> #float
  val atanh : #float -> #float
  val erf : #float -> #float
  val erfc : #float -> #float
  val trunc : #float -> #float
  val round : #float -> #float
  val ceil : #float -> #float
  val floor : #float -> #float
  val next_after : #float -> #float -> #float
  val copy_sign : #float -> #float -> #float
  val sign_bit : #float -> bool
(* CR reisenberg: this doesn't parse yet
  val frexp : #float -> (# #float * int #)   (* Part of v7 *)
*)
  val ldexp : #float -> int -> #float
(* CR reisenberg: this doesn't parse yet
  val modf : #float -> (# #float * #float #) (* Part of v7 *)
*)

  type t = #float

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val min : t -> t -> t
  val max : #float -> #float -> #float
(* CR reisenberg: this doesn't parse yet
  val min_max : #float -> #float -> (# #float * #float #) (* Part of v7 *)
*)
  val min_num : t -> t -> t
  val max_num : t -> t -> t
  val min_max_num : #float -> #float -> #float * #float (* Part of v5 *)
(* NB: [min_max_num] returns a boxed tuple to match the general interface *)

  val hash : t -> int

(* Part of v4; the [#unit]s will be [unit] before v5 *)
  module Array : sig
    type t
(* not sure what t will equal; possibly [#float array]; to be filled in *)

    val length : t -> int
    val get : t -> int -> #float
    val set : t -> int -> #float -> #unit
    val make : int -> #float -> t
    val create : int -> t
    val init : int -> (int -> #float) -> t
    val append : t -> t -> t
    val concat : t list -> t
    val sub : t -> int -> int -> t
    val copy : t -> t
    val fill : t -> int -> int -> #float -> #unit
    val blit : t -> int -> t -> int -> int -> #unit
(* no [to_list] or [of_list]; we don't have lists of unboxed things *)
    val iter : (#float -> #unit) -> t -> #unit
    val iteri : (int -> #float -> #unit) -> t -> #unit
    val map : (#float -> #float) -> t -> t
    val mapi : (int -> #float -> #float) -> t -> t
    val fold_left : ('a -> #float -> 'a) -> 'a -> t -> 'a
    val fold_right : (#float -> 'a -> 'a) -> t -> 'a -> 'a
    val iter2 : (#float -> #float -> #unit) -> t -> t -> #unit
    val map2 : (#float -> #float -> #float) -> t -> t -> t
    val for_all : (#float -> bool) -> t -> bool
    val exists : (#float -> bool) -> t -> bool
    val mem : #float -> t -> bool
    val mem_ieee : #float -> t -> bool

    val sort : (#float -> #float -> int) -> t -> #unit
    val stable_sort : (#float -> #float -> int) -> t -> #unit
    val fast_sort : (#float -> #float -> int) -> t -> #unit

(* no [to_seq], [to_seqi], or [of_seq]; we don't have [Seq]s of unboxed things *)

    val map_to_array : (#float -> 'a) -> t -> 'a array
    val map_from_array : ('a -> #float) -> 'a array -> t

(* CR reisenberg: this doesn't parse yet
    val map_to_bits32_array : ('a : bits32). (#float -> 'a) -> t -> 'a array
    val map_from_bits32_array : ('a : bits32). ('a -> #float) -> 'a array -> t
   *)
(* RAE XXX should we add more here? *)

  end

(* Part of v4; the [#unit]s will be [unit] before v5 *)
  module ArrayLabels : sig
    type t = Array.t

    val length : t -> int
    val get : t -> int -> #float
    val set : t -> int -> #float -> #unit
    val make : int -> #float -> t
    val create : int -> t
    val init : int -> f:(int -> #float) -> t
    val append : t -> t -> t
    val concat : t list -> t
    val sub : t -> pos:int -> len:int -> t
    val copy : t -> t
    val fill : t -> pos:int -> len:int -> #float -> #unit
    val blit : src:t -> src_pos:int -> dst:t -> dst_pos:int -> len:int -> #unit
(* no [to_list] or [of_list]; we don't have lists of unboxed things *)
    val iter : f:(#float -> #unit) -> t -> #unit
    val iteri : f:(int -> #float -> #unit) -> t -> #unit
    val map : f:(#float -> #float) -> t -> t
    val mapi : f:(int -> #float -> #float) -> t -> t
    val fold_left : f:('a -> #float -> 'a) -> init:'a -> t -> 'a
    val fold_right : f:(#float -> 'a -> 'a) -> t -> init:'a -> 'a
    val iter2 : f:(#float -> #float -> #unit) -> t -> t -> #unit
    val map2 : f:(#float -> #float -> #float) -> t -> t -> t
    val for_all : f:(#float -> bool) -> t -> bool
    val exists : f:(#float -> bool) -> t -> bool
    val mem : #float -> set:t -> bool
    val mem_ieee : #float -> set:t -> bool

    val sort : cmp:(#float -> #float -> int) -> t -> #unit
    val stable_sort : cmp:(#float -> #float -> int) -> t -> #unit
    val fast_sort : cmp:(#float -> #float -> int) -> t -> #unit

(* no [to_seq], [to_seqi], or [of_seq]; we don't have [Seq]s of unboxed things *)

    val map_to_array : f:(#float -> 'a) -> t -> 'a array
    val map_from_array : f:('a -> #float) -> 'a array -> t

(* CR reisenberg: this doesn't parse yet
    val map_to_bits32_array : f:('a : bits32). (#float -> 'a) -> t -> 'a array
    val map_from_bits32_array : f:('a : bits32). ('a -> #float) -> 'a array -> t
*)
  end
end

module Ufloat : Ufloat = Ufloat

[%%expect {|
Line 2, characters 13-18:
2 |   val (+) : #float -> #float -> #float
                 ^^^^^
Error: Unbound class type float
|}]
(* CR reisenberg: there should be no errors here *)

(* CR reisenberg: this doesn't parse yet

let x = #3.14
let x = Ufloat.(#3.14 + #2.78)
let x = #0.14
let x = #1.

[%%expect {|
??
|}]

let bad = #3.14 + #2.15

[%%expect {|
error
|}]

let bad = #3.14 +. 2.15

[%%expect {|
error
|}]

let bad = Ufloat.(#3.14+#2.15)  (* the [+#] is parsed as one lexeme *)

[%%expect {|
error
|}]

let f x y = Ufloat.(x + y)

[%%expect {|
??
|}]

let x = f #3.14 #2.15
let x = f #1. #1.
let g x = f x x

[%%expect {|
??
|}]

let bad = f 1. 2.

[%%expect {|
error
|}]

*)
