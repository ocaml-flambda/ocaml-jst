(** Supporting functions for list comprehensions *)

(** List comprehensions are desugared in terms of difference lists, functions
    from ['a list -> 'a list], which have been built in reverse *)
type 'a rev_dlist = 'a list -> 'a list

(** Reverse a list.  To turn a reversed difference list into a (normal,
    forwards) list, first provide it the empty list and then reverse the
    result. *)
val rev : 'a list -> 'a list

(** [rev_dlist_concat_map] is [concat_map] for reversed difference lists *)
val rev_dlist_concat_map : ('a -> 'b rev_dlist) -> 'a list -> 'b rev_dlist

(** [rev_dlist_concat_iterate_up f low high] is the same as
    [rev_dlist_concat_map f] over the range from [low] to [high], inclusive *)
val rev_dlist_concat_iterate_up
  : (int -> 'a rev_dlist) -> int -> int -> 'a rev_dlist

(** [rev_dlist_concat_iterate_up f low high] is the same as
    [rev_dlist_concat_map f] over the range from [high] to [low], inclusive *)
val rev_dlist_concat_iterate_down
  : (int -> 'a rev_dlist) -> int -> int -> 'a rev_dlist
