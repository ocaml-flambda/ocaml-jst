(* TEST
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
 *)

(* Goal: test to make sure that calls to primitive functions do not
   allocate. *)

(* put this in a function to avoid the number showing up in the expect-test. *)
(* NB: right-to-left evaluation order gets this right *)
let baseline_allocation () = Gc.allocated_bytes() -. Gc.allocated_bytes()

[%%expect {|
success
|}]

let alloc =
  let before = Gc.allocated_bytes() in
  let f = Ufloat.cos #0.0 in
  let after = Gc.allocated_bytes() in
  (after -. before) -. baseline_allocation ()

[%%expect {|
0
|}]

let alloc =
  let before = Gc.allocated_bytes() in
  let f = Ufloat.(#2.1 + #3.4) in
  let after = Gc.allocated_bytes() in
  (after -. before) -. baseline_allocation ()

[%%expect {|
0
|}]
