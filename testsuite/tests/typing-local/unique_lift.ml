(* TEST
   flags += "-extension unique"
 * native
   reference = "${test_source_directory}/unique_lift.reference"
*)

type point = { dim : int; x : float; y : float; z : float }

let constant_lift b =
  let unique_ p = { dim = 3; x = 1.0; y = 2.0; z = 3.0 } in
  if b then p else { unique_ p with x = 2.0 }

type fpoint = { x : float; y : float; z : float }

let fconstant_lift b =
  let unique_ p = { x = 1.0; y = 2.0; z = 3.0 } in
  if b then p else { unique_ p with x = 2.0 }

let () =
  Printf.printf "%f %f %f\n" ((constant_lift true).x) ((constant_lift false).x) ((constant_lift true).x);
  Printf.printf "%f %f %f\n" ((fconstant_lift true).x) ((fconstant_lift false).x) ((fconstant_lift true).x)
