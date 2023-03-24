(* TEST
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
*)
(* CR layouts (v2): enable this test *)

let f : #int64 -> #int64 = fun x -> Uint64.(x + #3L)
let y = f #4L

[%%expect {|
success
|}]

let f x = Uint64.(x + #3L)
let y = f #4L

[%%expect {|
success
|}]

(* CR layouts: reisenberg: actually, not sure whether these should work *)
let y = f @@ #4L
let y = #4L |> f

[%%expect {|
success
|}]

let twice f x = f (f x)

[%%expect {|
success
|}]

let y = twice f #4L

[%%expect {|
error
|}]

let twice f (x : ('a : bits64)) = f (f x)

[%%expect {|
success
|}]

let y = twice f #4L

[%%expect {|
success
|}]

let y = twice (Int.add 3) 4

[%%expect {|
error
|}]

let twice f (x : ('a : bits32)) = f (f x)
let y = twice (fun x -> Uint32.add x #3l) #4l
let y = twice (Uint32.add #2l) #4l

[%%expect {|
success
|}]

let twice f (x : ('a : float64)) = f (f x)
let y = twice (fun x -> Ufloat.add x #3.) #4.

[%%expect {|
success
|}]

let twice f (x : ('a : word)) = f (f x)
let y = twice (fun x -> Unativeint.add x #3n) #4n

[%%expect {|
success
|}]

let infer =
  let t f x = f (f x) in
  t f #4L

[%%expect {|
success
|}]

let compose f g x = f (g (x : ('a : bits64)))

[%%expect {|
success
|}]

let y = compose (fun x -> x) (fun x -> x) #4L

[%%expect {|
success
|}]

let y = compose (fun x -> x) (fun x -> x) #4l

[%%expect {|
error
|}]

let y = compose Uint64.succ Uint64.pred #4L

[%%expect {|
success
|}]

let f (x : #int64) =
  let () = Sys.opaque_identity () in
  let g (y : #int64) =
    let x' = Uint64.to_int64 x in
    let y' = Uint64.to_int64 y in
    let r = Int64.add x' y' in
    Uint64.of_int64 r
  in
  let () = Sys.opaque_identity () in
  g

[%%expect {|
success
|}]

let f (x : #int64) (y : #int64) : #int64 =
  let i : #int64 = Uint64.of_int64
                     (Int64.add (Uint64.to_int64 x) (Uint64.to_int64 y)) in
  Uint64.of_int64 (Int64.mul (Uint64.to_int64 i) (Uint64.to_int64 i))

let[@inline never] g i : #int64 -> #int64 =
  f i

let () =
  let g = g #1234L in
  let n : #int64 = g #5678L in
  Uint64.to_int64 n

[%%expect {|
success
|}]

let f (x : #float) (y : #float) : #float =
  let i : #float = Ufloat.of_float
                     (Float.add (Ufloat.to_float x) (Ufloat.to_float y)) in
  Ufloat.of_float (Float.mul (Ufloat.to_float i) (Ufloat.to_float i))

let[@inline never] g i : #float -> #float =
  f i

let () =
  let g = g #1234. in
  let n : #float = g #5678. in
  Ufloat.to_float n

[%%expect {|
success
|}]
