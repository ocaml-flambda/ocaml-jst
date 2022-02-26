open Lambda
open Typedtree
open Debuginfo.Scoped_location

(** Translate array comprehensions; see the .ml file for more details *)

val comprehension
  :  transl_exp:(scopes:scopes -> expression -> lambda)
  -> scopes:scopes
  -> loc:scoped_location
  -> array_kind:array_kind
  -> comprehension
  -> lambda

(* CR aspectorzabusky: Needs to be factored out so it can be shared properly with
   [Transl_list_comprehension] *)
module Lambda_utils : sig
  module Make : sig
    val int    : int -> lambda
    val float  : float -> lambda
    val string : loc:Location.t -> string -> lambda
  end

  module type Int_ops = sig
    (* We want to expose all the operators so we don't have to think about which
       ones to add and remove as we change the rest of the file *)
    [@@@warning "-unused-value-declaration"]

    (** Integer arithmetic *)

    val ( + ) : lambda -> lambda -> lambda
    val ( - ) : lambda -> lambda -> lambda
    val ( * ) : lambda -> lambda -> lambda
    val ( / ) : lambda -> lambda -> lambda

    (** Integer comparisons *)

    val ( = )  : lambda -> lambda -> lambda
    val ( <> ) : lambda -> lambda -> lambda
    val ( < )  : lambda -> lambda -> lambda
    val ( > )  : lambda -> lambda -> lambda
    val ( <= ) : lambda -> lambda -> lambda
    val ( >= ) : lambda -> lambda -> lambda

    (** Boolean logical operators *)

    val ( && ) : lambda -> lambda -> lambda
    val ( || ) : lambda -> lambda -> lambda

    (** Integer literals *)
    val l0 : lambda
    val l1 : lambda
    val i  : int -> lambda
  end

  val int_ops : loc:scoped_location -> (module Int_ops)

  module Primitive : sig
    (** [make_vect ~length ~init] calls the [caml_make_vect] C primitive, which
        creates an array of the given [length] containing that many copies of
        the given [init]ial value *)
    val make_vect :
      loc:scoped_location -> length:lambda -> init:lambda -> lambda

    (** [make_float_vect len] calls the [caml_make_float_vect] C primitive,
        which creates an unboxed float array of length [len] whose contents are
        uninitialized *)
    val make_float_vect : loc:scoped_location -> lambda -> lambda

    (** [array_append a1 a2] calls the [caml_array_append] C primitive, which
        creates a new array by appending [a1] and [a2] *)
    val array_append : loc:scoped_location -> lambda -> lambda -> lambda

    (** [array_sub a ~offset ~length] calls the [caml_array_sub] C primitive,
        which creates a new subarray corresponding to the subarray of [a]
        starting at the given [offset] with the given [length] *)
    val array_sub :
      loc:scoped_location -> lambda -> offset:lambda -> length:lambda -> lambda
  end
end

(* CR aspectorzabusky: Needs to be factored out so it can be shared properly with
   [Transl_list_comprehension] *)
module Cps_utils : sig
  (** [compose_map f xs] applies [f] to every element of [xs], obtaining a list
      of functions, and then composes these functions (from left to right).
      This is useful for, e.g., combining a sequence of translated clauses into
      a single [lambda -> lambda] function. *)
  val compose_map : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

  (** [compose_map_acc f xs] is like [compose_map], but [f] returns a pair of a
      function and some extra data; the final result is then the composition (as
      in [compose_map]) paired with the list of all these extra values.  This is
      useful for combining a sequence of iterators into a single [lambda ->
      lambda] function and their list of generated bindings (a
      ['u Iterator_bindings.t list]), as the [binding] function returns this
      extra data. *)
  val compose_map_acc :
    ('a -> ('b -> 'b) * 'c) -> 'a list -> ('b -> 'b) * 'c list
end
