(* TEST
   * native *)

external local_stack_offset : unit -> int = "caml_local_stack_offset"
external opaque_local : ('a[@local_opt]) -> ('a[@local_opt]) = "%opaque"

let check_expected_offsets (name,actual,expected) =
  let p xs = String.concat "; " (List.map Int.to_string xs) in
  if List.equal (=) actual expected then
    Printf.printf "%25s: OK\n%!" name
  else
    Printf.printf "%25s: Error.  Expected: [%s],  Saw: [%s]\n%!"
      name (p expected) (p actual)

(* local_ for allocates in parent region *)
let loc_for () =
  let offset_loop = ref (-1) in
  let offset1 = local_stack_offset () in
  for i = 0 to 0 do local_
    let z = local_ (Some (Sys.opaque_identity 42)) in
    let _ = (opaque_local z) in
    offset_loop := local_stack_offset ()
  done;
  let offset2 = local_stack_offset () in
  [offset1; !offset_loop; offset2]

let loc_for_expect = [0; 16; 16]

(* Non local loop allocates in its own region *)
let nonloc_for () =
  let offset_loop = ref (-1) in
  let offset1 = local_stack_offset () in
  for i = 0 to 0 do
    let z = local_ (Some (Sys.opaque_identity 42)) in
    let _ = (opaque_local z) in
    offset_loop := local_stack_offset ()
  done;
  let offset2 = local_stack_offset () in
  [offset1; !offset_loop; offset2]

let nonloc_for_expect = [0; 16; 0]

(* Local while body should allocate in parent *)
let loc_while_body () =
  let offset_loop = ref (-1) in
  let offset1 = local_stack_offset () in
  let cond = ref true in
  while !cond do local_
    let z = local_ (Some (Sys.opaque_identity 42)) in
    let _ = (opaque_local z) in
    offset_loop := local_stack_offset ();
    cond := false
  done;
  let offset2 = local_stack_offset () in
  [offset1; !offset_loop; offset2]

let loc_while_body_expect = [0;16;16]

(* Nonlocal while body should allocate in its own region*)
let nonloc_while_body () =
  let offset_loop = ref (-1) in
  let offset1 = local_stack_offset () in
  let cond = ref true in
  while !cond do
    let z = local_ (Some (Sys.opaque_identity 42)) in
    let _ = (opaque_local z) in
    offset_loop := local_stack_offset ();
    cond := false
  done;
  let offset2 = local_stack_offset () in
  [offset1; !offset_loop; offset2]

let nonloc_while_body_expect = [0;16;0]

(* Local while condition should allocate in parent *)
let loc_while_cond () =
  let offset_loop = ref (-1) in
  let offset1 = local_stack_offset () in
  while local_
    let z = local_ (Some (Sys.opaque_identity 42)) in
    let _ = (opaque_local z) in
    offset_loop := local_stack_offset ();
    false
  do
    ()
  done;
  let offset2 = local_stack_offset () in
  [offset1; !offset_loop; offset2]

let loc_while_cond_expect = [0;16;16]

(* Nonlocal while condition should allocate in its own region *)
let nonloc_while_cond () =
  let offset_loop = ref (-1) in
  let offset1 = local_stack_offset () in
  while
    let z = local_ (Some (Sys.opaque_identity 42)) in
    let _ = (opaque_local z) in
    offset_loop := local_stack_offset ();
    false
  do
    ()
  done;
  let offset2 = local_stack_offset () in
  [offset1; !offset_loop; offset2]

let nonloc_while_cond_expect = [0;16;0]

let () =
  List.iter check_expected_offsets [
    "local for",           loc_for (),           loc_for_expect;
    "non-local for",       nonloc_for (),        nonloc_for_expect;
    "local while body",    loc_while_body (),    loc_while_body_expect;
    "nonlocal while body", nonloc_while_body (), nonloc_while_body_expect;
    "local while cond",    loc_while_cond (),    loc_while_cond_expect;
    "nonlocal while cond", nonloc_while_cond (), nonloc_while_cond_expect;
  ]
