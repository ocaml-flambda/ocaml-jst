(* TEST
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
*)

(* CR reisenberg: change [unit] to [#unit] in v5 *)
module type Array = sig
  module Uint64 : sig
    type 'a t = 'a array
    val length : 'a array -> #int64
    val get : 'a array -> #int64 -> 'a
    val set : 'a array -> #int64 -> 'a -> unit
    val make : #int64 -> 'a -> 'a array
    val create : #int64 -> 'a -> 'a array
    val create_float : #int64 -> float array
    val make_float : #int64 -> float array
    val init : #int64 -> (#int64 -> 'a) -> 'a array
    val make_matrix : #int64 -> #int64 -> 'a -> 'a array array
    val create_matrix : #int64 -> #int64 -> 'a -> 'a array array
    val sub : 'a array -> #int64 -> #int64 -> 'a array
    val fill : 'a array -> #int64 -> #int64 -> 'a -> unit
    val blit : 'a array -> #int64 -> 'a array -> #int64 -> #int64 -> unit
    val iteri : (#int64 -> 'a -> unit) -> 'a array -> unit
    val mapi : (#int64 -> 'a -> 'b) -> 'a array -> 'b array
  end

  module Uint32 : sig
    type 'a t = 'a array
    val length : 'a array -> #int32
    val get : 'a array -> #int32 -> 'a
    val set : 'a array -> #int32 -> 'a -> unit
    val make : #int32 -> 'a -> 'a array
    val create : #int32 -> 'a -> 'a array
    val create_float : #int32 -> float array
    val make_float : #int32 -> float array
    val init : #int32 -> (#int32 -> 'a) -> 'a array
    val make_matrix : #int32 -> #int32 -> 'a -> 'a array array
    val create_matrix : #int32 -> #int32 -> 'a -> 'a array array
    val sub : 'a array -> #int32 -> #int32 -> 'a array
    val fill : 'a array -> #int32 -> #int32 -> 'a -> unit
    val blit : 'a array -> #int32 -> 'a array -> #int32 -> #int32 -> unit
    val iteri : (#int32 -> 'a -> unit) -> 'a array -> unit
    val mapi : (#int32 -> 'a -> 'b) -> 'a array -> 'b array
  end

  module Unativeint : sig
    type 'a t = 'a array
    val length : 'a array -> #nativeint
    val get : 'a array -> #nativeint -> 'a
    val set : 'a array -> #nativeint -> 'a -> unit
    val make : #nativeint -> 'a -> 'a array
    val create : #nativeint -> 'a -> 'a array
    val create_float : #nativeint -> float array
    val make_float : #nativeint -> float array
    val init : #nativeint -> (#nativeint -> 'a) -> 'a array
    val make_matrix : #nativeint -> #nativeint -> 'a -> 'a array array
    val create_matrix : #nativeint -> #nativeint -> 'a -> 'a array array
    val sub : 'a array -> #nativeint -> #nativeint -> 'a array
    val fill : 'a array -> #nativeint -> #nativeint -> 'a -> unit
    val blit : 'a array -> #nativeint -> 'a array -> #nativeint -> #nativeint -> unit
    val iteri : (#nativeint -> 'a -> unit) -> 'a array -> unit
    val mapi : (#nativeint -> 'a -> 'b) -> 'a array -> 'b array
  end
end

module Array : Array = Array

[%%expect{|
success
|}]

(* CR reisenberg: These also need correctness tests, which will be added. *)

