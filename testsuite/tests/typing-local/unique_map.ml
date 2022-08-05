(* TEST
   flags += "-extension unique"
 * native
   reference = "${test_source_directory}/unique_map.reference"
 *)

type 'a list =
  | Cons of { hd : 'a; tl : 'a list }
  | Nil

let rec map f (unique_ xs) =
  match xs with
  | Nil -> xs
  | Cons ({hd;tl} as xs) -> Cons { unique_ xs with hd = f hd; tl = map f tl }

let () =
  let xs = Cons { hd = 1; tl = Cons { hd = 2; tl = Cons { hd = 3; tl = Nil } } } in

  let prebefore = Gc.allocated_bytes () in
  let before = Gc.allocated_bytes () in
  let _ = Sys.opaque_identity (map (fun x -> x + 1) xs) in
  let after = Gc.allocated_bytes () in
  let delta =
    int_of_float ((after -. before) -. (before -. prebefore))
    / (Sys.word_size/8)
  in
  let msg =
    match delta with
    | 0 -> "No Allocation"
    | n -> "Allocation"
  in
  Printf.printf "%15s: %s\n" "List.map" msg

