(* TEST
   flags += "-extension unique"
 * skip
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
  let xs = map (fun x -> x * 2) xs in
  let after = Gc.allocated_bytes () in
  let delta =
    int_of_float ((after -. before) -. (before -. prebefore))
    / (Sys.word_size/8)
  in
  let xs_ref = Cons { hd = 2; tl = Cons { hd = 4; tl = Cons { hd = 6; tl = Nil } } } in
  assert (xs = xs_ref);
  assert (delta = 0);