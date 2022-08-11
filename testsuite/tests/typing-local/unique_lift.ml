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
  let x = (constant_lift true).x in
  let y = (constant_lift false).x in
  let z = (constant_lift true).x in
  Printf.printf "%f %f %f\n" x y z;
  let x = (fconstant_lift true).x in
  let y = (fconstant_lift false).x in
  let z = (fconstant_lift true).x in
  Printf.printf "%f %f %f\n" x y z
