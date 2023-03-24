(* TEST
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
 *)

(* Goal: test to make sure that calls to primitive functions do not
   allocate. *)

let measure_alloc f =
  (* NB: right-to-left evaluation order gets this right *)
  let baseline_allocation = Gc.allocated_bytes() -. Gc.allocated_bytes() in
  let before = Gc.allocated_bytes () in
  f ();
  let after = Gc.allocated_bytes () in
  (after -. before) -. baseline_allocation

[%%expect {|
success
|}]

let alloc =
  measure_alloc (fun () -> let f = Ufloat.cos #0.0 in
                                     ignore (Sys.opaque_identity f))

[%%expect {|
0
|}]

let alloc =
  measure_alloc (fun () -> let f = Ufloat.(#2.1 + #3.4) in
                                           ignore (Sys.opaque_identity f))

[%%expect {|
0
|}]
