(* TEST
  * skip
   reason = "Unboxed types v4 isn't implemented yet"
  ** expect
*)
(* CR layouts (v4): Enable this test *)

(* CR layouts (v5): remove the unit arguments, which are just there because
   we can't put unboxed types into modules yet *)
let f () : #float = #4.0
let ni () : #nativeint = #42n
let i64 () : #int64 = #42L
let i32 () : #int32 = #42l

[%%expect {|
success
|}]

let f' : float = box (f ())
let ni' : nativeint = box (ni ())
let i64' : int64 = box (i64 ())
let i32' : int32 = box (i32 ())

[%%expect {|
success
|}]

type (_, _) eq = Refl : ('a, 'a) eq

[%%expect {|
success
|}]

let p : (float, #float box) eq = Refl
let p : (nativeint, #nativeint box) eq = Refl
let p : (int64, #int64 box) eq = Refl
let p : (int32, #int32 box) eq = Refl

[%%expect {|
success
|}]

let b = Ufloat.equal (unbox 3.14) #3.14
let b = Unativeint.equal (unbox 42n) #42n
let b = Uint64.equal (unbox 42L) #42L
let b = Uint32.equal (unbox 42l) #42l

[%%expect {|
all true
|}]

let x : int64 or_null = Some (box #4n)
let fs : #float box list = [box #2.78; box #3.14]

[%%expect {|
success
|}]

let wrapped = box (box "hello")

[%%expect {|
success, with type string box box
|}]

let mybox x = box x
let myunbox x = unbox x

[%%expect {|
val mybox : 'a -> 'a box
val myunbox : 'a box -> 'a
|}]

let mybox (x : #float) = box x
let myunbox (x : float) = unbox x

[%%expect {|
val mybox : #float -> float
val myunbox : float -> #float
|}]

let mybox (x : ('a : float64)) = box x
let myunbox x : ('a : float64) = unbox x

[%%expect {|
val mybox : ('a : float64). 'a -> 'a box
val myunbox : ('a : float64). 'a box -> 'a
|}]

let mybox (x : ('a : any)) = box x
let myunbox x : ('a : any) = unbox x

[%%expect {|
val mybox : 'a -> 'a box
val myunbox : 'a box -> 'a
|}]

let mybox : ('a : any). 'a -> 'a box = fun x -> box x

[%%expect {|
fail
|}]

let myunbox : ('a : any). 'a box -> 'a = fun x -> unbox x

[%%expect {|
fail
|}]

let mybox = box
let myunbox = unbox

[%%expect {|
not sure;
probably should succeed with type ('a : value). 'a -> 'a box, but a failure is OK here
|}]

let mybox : ('a : any). 'a -> 'a box = box

[%%expect {|
fail: cannot use [box] at [any]
|}]

let myunbox : ('a : any). 'a box -> 'a = unbox

[%%expect {|
fail
|}]

type 'a mybox = 'a box

[%%expect {|
type ('a : any) mybox = 'a box
|}]

type ('a : any) mybox : non_null_value = 'a box

[%%expect {|
type ('a : any) mybox = 'a box
|}]

(* test the float array optimization with boxed #floats *)

let arr1 = [| box #3.14; box #5.16 |]
let good = Obj.tag (Obj.repr arr1) = Obj.double_array_tag

let mk x = [| x |]
let arr2 = mk (box #2.78)
let good = Obj.tag (Obj.repr arr2) = Obj.double_array_tag

[%%expect {|
good = true
good = true
|}]

(* CR layouts (v4): add quickcheck-style tests to ensure that
   box and unbox are inverses *)
