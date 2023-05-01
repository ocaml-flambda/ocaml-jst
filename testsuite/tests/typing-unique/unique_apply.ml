(* TEST
   flags += "-extension unique"
 * native
*)

(* regression test *)
(* This test used to fail to compile when uniqueness information was included in the
   description of the caml_apply functions, causing the dedup to fail. *)

let unique_work ~insert ~fold ~empty =
  let rec loop n (unique_ t) =
    if n <= 0 then t
    else loop (n - 1) (insert n (n mod 10 = 0) t) in
  let unique_ tree = loop 4200000 empty in
  fold (fun _ v acc -> if v then acc + 1 else acc) 0 tree

let rec loop insert (unique_ t) = loop insert (insert 0 t)
