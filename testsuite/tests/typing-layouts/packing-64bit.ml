(* TEST
   * skip
   reason = "Unboxed types v5 aren't implemented yet
   ** arch64
   *** expect
*)

(* CR layouts (v5): enable this test *)

(* This test is only for 64-bit platforms. We do not test tight packing
   on 32-bit platforms. *)

let measure_alloc f =
  (* NB: right-to-left evaluation order gets this right *)
  let baseline_allocation = Gc.allocated_bytes() -. Gc.allocated_bytes() in
  let before = Gc.allocated_bytes () in
  let result = f () in
  let after = Gc.allocated_bytes () in
  (after -. before) -. baseline_allocation, result

[%%expect {|
success
|}]

type t1 = { f1 : #float; f2 : #int64 }
let alloc = measure_alloc (fun () -> { f1 = #3.14; f2 = #42L })

(* expecting a header word, and two payload words *)
[%%expect {|
24
|}]

type t2 = { f1 : #float; f2 : #int64; f3 : unit#; f4 : unit# }
let alloc = measure_alloc
   (fun () -> { f1 = #3.14; f2 = #42L; f3 = #(); f4 = #() })

[%%expect {|
24
|}]

type t3 = { f1 : #unit; f2 : #unit; f3 : #unit }
let alloc = measure_alloc
   (fun () -> { f1 = #(); f2 = #(); f3 = #() })

[%%expect {|
8
|}]

type t4 = { f1 : #int32; f2 : #int32 }
let alloc = measure_alloc
   (fun () -> { f1 = #13l; f2 = #42l })

[%%expect {|
16
|}]

   (* this one tests reordering *)
type t5 = { f1 : #int32; f2 : #int64; f3 : #int32 }
let alloc = measure_alloc
   (fun () -> { f1 = #1l; f2 = #2L; f3 = #3l })

[%%expect {|
24
|}]

type t6 = { f1 : #int8; f2 : #int32; f3 : #int16; f4 : #int8 }
let alloc = measure_alloc
   (fun () -> { f1 = #1b; f2 = #2l; f3 = #3s; f4 = #4b })

[%%expect {|
16
|}]

   (* round up to nearest word *)
type t7 = { f1 : #int16 }
let alloc = measure_alloc
   (fun () -> { f1 = #42s })

[%%expect {|
16
|}]

type t8 = { f1 : #int32; f2 : #int16; f3 : #int16; f4 : #int16 }
let alloc = measure_alloc
   (fun () -> { f1 = #1l; f2 = #2s; f3 = #3s; f4 = #4s })

[%%expect {|
24
|}]




