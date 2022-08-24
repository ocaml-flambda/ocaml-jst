open Lambda

(** First-class let bindings; we sometimes need to collect these while
    translating array comprehension clauses and bind them later. *)
module Let_binding : sig
  (** The first-class (in OCaml) type of let bindings. *)
  type t =
    { let_kind   : let_kind
    ; value_kind : value_kind
    ; id         : Ident.t
    ; init       : lambda }

  (** Create a fresh local identifier to bind (from a string), and return that
      it along with the Lambda variable (with [Lvar]) for it and the
      corresponding let binding. *)
  val make_id_var :
    let_kind -> value_kind -> string -> lambda -> Ident.t * lambda * t

  (** Create a fresh local identifier to bind (from a string), and return it
      along with the corresponding let binding. *)
  val make_id : let_kind -> value_kind -> string -> lambda -> Ident.t * t

  (** Create a fresh local identifier to bind (from a string), and return its
      corresponding Lambda variable (with [Lvar]) and let binding. *)
  val make_var : let_kind -> value_kind -> string -> lambda -> lambda * t

  (** Create a Lambda let-binding (with [Llet]) from a first-class let
      binding, providing the body. *)
  val let_one : t -> lambda -> lambda

  (** Create Lambda let-bindings (with [Llet]) from multiple first-class let
      bindings, providing the body. *)
  val let_all : t list -> lambda -> lambda
end

(** Convenience functions for working with the Lambda AST *)
module Lambda_utils : sig
  (** Creating AST fragments from OCaml values *)
  module Make : sig
    (** Lambda integer literals *)
    val int    : int -> lambda

    (** Lambda float literals; be careful with unusual values, as this calls
        [Float.to_string] *)
    val float  : float -> lambda

    (** Lambda string literals; these require a location, and are constructed as
        "quoted strings", not {fancy|delimited strings|fancy}. *)
    val string : loc:Location.t -> string -> lambda
  end

  (** Apply a Lambda function to some Lambda values, at a location; all the
      other information needed by [Lapply] can be defaulted away and ignored. *)
  val apply :
    ?tailcall:tailcall_attribute ->
    ?inlined:inlined_attribute ->
    ?specialised:specialise_attribute ->
    ?probe:probe_desc ->
    loc:scoped_location ->
    lambda -> lambda list -> lambda

  (** Nicer OCaml syntax for constructing Lambda ASTs that operate on integers;
      created by [int_ops], which includes the necessary location in all the
      operations *)
  module type Int_ops = sig
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

  (** Construct an [Int_ops] module at the given location *)
  val int_ops : loc:scoped_location -> (module Int_ops)

  (** Expose functions to construct Lambda calls to primitives; some of their
      arguments have been given labels, but otherwise they mirror the primitives
      exactly *)
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
