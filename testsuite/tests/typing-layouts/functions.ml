(* TEST
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
*)

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

(* CR reisenberg: actually, not sure whether these should work *)
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
