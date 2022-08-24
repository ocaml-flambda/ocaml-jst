open! Stdlib

type 'a rev_dlist = 'a list -> 'a list

let rev = List.rev

(* Can be thought of as the combination of [map] and composition *)
let rev_dlist_concat_map l f acc =
  List.fold_left (fun acc el -> f el acc) acc l

(* CR aspectorzabusky: At one point these functions were structured as
   [let ... = let rec loop ... in loop ...], and I just inlined the [loop]
   because it wasn't doing anything.   But were there efficiency reasons I
   missed? *)

let rec rev_dlist_concat_iterate_up from to_ f acc =
  if to_ < from
  then acc
  else rev_dlist_concat_iterate_up (from + 1) to_ f (f from acc)
;;

let rec rev_dlist_concat_iterate_down from to_ f acc =
  if to_ > from
  then acc
  else rev_dlist_concat_iterate_down (from - 1) to_ f (f from acc)
;;
