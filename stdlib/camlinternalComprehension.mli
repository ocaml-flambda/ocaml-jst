(** Supporting functions for list comprehensions *)

(** List comprehensions are desugared in terms of difference lists, functions
    from ['a list -> 'a list], which have been built in reverse. *)
type 'a rev_dlist = 'a list -> 'a list

(** Reverse a list.  To turn a reversed difference list into a (normal,
    forwards) list, first provide it the empty list and then reverse the
    result. *)
val rev : 'a list -> 'a list

(** [rev_dlist_concat_map] is [concat_map] with its arguments swapped for
    reversed difference lists. *)
val rev_dlist_concat_map : 'a list -> ('a -> 'b rev_dlist) -> 'b rev_dlist

(** [rev_dlist_concat_iterate_up low high f] is the same as
    [rev_dlist_concat_map range f] where [range] is the increasing range from
    [low] to [high], inclusive. *)
val rev_dlist_concat_iterate_up
  : int -> int -> (int -> 'a rev_dlist) -> 'a rev_dlist

(** [rev_dlist_concat_iterate_up high low f] is the same as
    [rev_dlist_concat_map range f] where [range] is the decreasing range from
    [high] to [low], inclusive. *)
val rev_dlist_concat_iterate_down
  : int -> int -> (int -> 'a rev_dlist) -> 'a rev_dlist
