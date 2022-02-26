open! Stdlib

type 'a rev_dlist = 'a list -> 'a list

let rev = List.rev

(* Can be thought of as the combination of [map] and composition *)
let rev_dlist_concat_map f l acc =
  List.fold_left (fun acc el -> f el acc) acc l

let rev_dlist_concat_iterate_up f from to_ acc =
  let rec loop f from to_ acc =
    if to_ < from
    then acc
    else loop f (from + 1) to_ (f from acc)
  in
  loop f from to_ acc
;;

let rev_dlist_concat_iterate_down f from to_ acc =
  let rec loop f from to_ acc =
    if to_ > from
    then acc
    else loop f (from - 1) to_ (f from acc)
  in
  loop f from to_ acc
;;
