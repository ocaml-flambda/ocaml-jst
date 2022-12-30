(* TEST
   * skip
   reason = "Unboxed types v4 not implemented yet"
   ** expect
*)
(* CR layouts (v4): enable this test *)

module type Array_Float64 = sig
  type ('a : float64) t = 'a array

  (* CR layouts (v5): Use #unit, not unit, below *)
  val length : ('a : float64). 'a array -> int
  val get : ('a : float64). 'a array -> int -> 'a
  val set : ('a : float64). 'a aray -> int -> 'a -> unit
  val make : ('a : float64). int -> 'a -> 'a array
  val init : ('a : float64). int -> (int -> 'a) -> 'a array
  val make_matrix : ('a : float64). int -> int -> 'a -> 'a array array
  val append : ('a : float64). 'a array -> 'a array -> 'a array
  val concat : ('a : float64). 'a array list -> 'a array
  val sub : ('a : float64). 'a array -> int -> int -> 'a array
  val copy : ('a : float64). 'a array -> 'a array
  val fill : ('a : float64). 'a array -> int -> int -> 'a -> unit
  val blit : ('a : float64). 'a array -> int -> 'a array -> int -> int -> unit

  val iter : ('a : float64). ('a -> unit) -> 'a array -> unit
  val iteri : ('a : float64). (int -> 'a -> unit) -> 'a array -> unit

  (* We're reserving the name [map] for the function that
     works layout-polymorphically *)

  val map_float64 :
    ('a : float64) ('b : float64). ('a -> 'b) -> 'a array -> 'b array

  val mapi_float64 :
    ('a : float64) ('b : float64). (int -> 'a -> 'b) -> 'a array -> 'b array
  val mapi_value :
    ('a : float64) ('b : value). (int -> 'a -> 'b) -> 'a array -> 'b array
  val mapi_bits64 :
    ('a : float64) ('b : bits64). (int -> 'a -> 'b) -> 'a array -> 'b array
  val mapi_bits32 :
    ('a : float64) ('b : bits32). (int -> 'a -> 'b) -> 'a array -> 'b array
  val mapi_bits16 :
    ('a : float64) ('b : bits16). (int -> 'a -> 'b) -> 'a array -> 'b array
  val mapi_bits8 :
    ('a : float64) ('b : bits8). (int -> 'a -> 'b) -> 'a array -> 'b array
  val mapi_nativeint :
    ('a : float64) ('b : nativeint). (int -> 'a -> 'b) -> 'a array -> 'b array

  val fold_left : ('a : value) ('b : float64). ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a

  val fold_left_map_value : ('a : value) ('b : float64) ('c : value).
    ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array

  val fold_right : ('a : value) ('b : float64). ('b -> 'a -> 'a) -> 'b array -> 'a -> 'a

  (* CR layouts (v4): add more function variants? *)

  val iter2_float64 : ('a : float64) ('b : float64).
    ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  val map2_float64_float64 : ('a : float64) ('b : float64) ('c : float64).
    ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array

  val for_all : ('a : float64). ('a -> bool) -> 'a array -> bool
  val exists : ('a : float64). ('a -> bool) -> 'a array -> bool
  val for_all2_float64 : ('a : float64) ('b : float64).
    ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val exists2_float64 : ('a : float64) ('b : float64).
    ('a -> 'b -> bool) -> 'a array -> 'b array -> bool

  (* No [mem] functions, because there is no polymorphic equality on
     unboxed types. And there is no physical equality either. *)

  (* CR layouts (v5): add these functions: *)
  val find_opt : ('a : float64). ('a -> bool) -> 'a array -> 'a option
  val find_map_float64 : ('a : float64) ('b : float64).
    ('a -> 'b option) -> 'a array -> 'b option

  (* CR layouts (v5): add these functions: *)
  val split_float64 : ('a : float64) ('b : float64).
    ('a * 'b) array -> 'a array * 'b array
  val combine_float64 : ('a : float64) ('b : float64).
    'a array -> 'b array -> ('a * 'b) array

  val sort : ('a : float64). ('a -> 'a -> int) -> 'a array -> unit
  val stable_sort : ('a : float64). ('a -> 'a -> int) -> 'a array -> unit
  val fast_sort : ('a : float64). ('a -> 'a -> int) -> 'a array -> unit
end

module Array_Float64 : Array_Float64 = Array.Float64

[%%expect {|
success
|}]

(* CR layouts (v4): add similar interfaces for other layouts once we
   have settled on the interface *)

(* CR layouts (v4): add quickcheck-style tests to ensure that the array
   functions work like the existing array functions *)

let arr1 : #float array = [| #3.14; #2.78 |]

[%%expect {|
success
|}]

let arr2 = [| #3.14; #2.78 |]

[%%expect {|
success, with type #float array
|}]

let arr3 : #float array = [| |]

[%%expect {|
success
|}]

let good = Obj.tag (Obj.repr arr2) = Obj.double_array_tag

[%%expect {|
true
|}]

let arr4 = [| #3n; #5n |]
let arr5 = [| #3L; #5L |]
let arr6 = [| #3l; #5l |]

[%%expect {|
 : #nativeint array
 : #int64 array
 : #int32 array
|}]

let good = Obj.tag (Obj.repr arr4) = Obj.first_non_constant_constructor_tag
let good = Obj.tag (Obj.repr arr5) = Obj.first_non_constant_constructor_tag
let good = Obj.tag (Obj.repr arr6) = Obj.first_non_constant_constructor_tag

[%%expect {|
true
true
true
|}]
