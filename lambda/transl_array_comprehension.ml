open Lambda
open Typedtree
open Asttypes
open Transl_comprehension_utils
open Lambda_utils.Make
open Lambda_utils.Primitive

(** Sometimes the generated code for array comprehensions reuses certain
    expressions more than once, and sometimes it uses them exactly once. We want
    to avoid using let bindings in the case where the expressions are used
    exactly once, so this module lets us check statically whether the let
    bindings have been created.

    The precise context is that the endpoints of integer ranges and the lengths
    of arrays are used once (as `for` loop endpoints) in the case where the
    array size is not fixed and the array has to be grown dynamically; however,
    they are used multiple times if the array size is fixed, as they are used to
    precompute the size of the newly-allocated array.  Because, in the
    fixed-size case, we need both the bare fact that the bindings exist as well
    as to do computation on these bindings, we can't simply maintain a list of
    bindings; thus, this module, allowing us to work with
    [(Usage.once, Let_binding.t) Usage.if_reused] in the dynamic-size case and
    [(Usage.many, Let_binding.t) Usage.if_reused] in the fixed-size case (as
    as similar [Usage.if_reused] types wrapping other binding-representing
    values). *)
module Usage = struct
  (** A two-state (boolean) type-level enum indicating whether a value is used
      exactly [once] or can be used [many] times *)

  type once = private Once [@@warning "-unused-constructor"]
  type many = private Many [@@warning "-unused-constructor"]

  (** The singleton reifying the above type-level enum, indicating whether
      values are to be used exactly [Once] or can be reused [Many] times *)
  type _ t =
    | Once : once t
    | Many : many t

  (** An option-like type for storing extra data that's necessary exactly when a
      value is to be reused [many] times *)
  type (_, 'a) if_reused =
    | Used_once : (once, 'a) if_reused
    | Reusable  : 'a -> (many, 'a) if_reused

  (** Wrap a value as [Reusable] iff we're in the [Many] case *)
  let if_reused (type u) (u : u t) (x : 'a) : (u, 'a) if_reused = match u with
    | Once -> Used_once
    | Many -> Reusable x

  (** Convert an [if_reused] to a [list], forgetting about the [once]/[many]
      distinction; the list is empty in the [Used_once] case and a singleton in
      the [Reusable] case. *)
  let list_of_reused (type u) : (u, 'a) if_reused -> 'a list = function
    | Used_once  -> []
    | Reusable x -> [x]
end

(** First-class let bindings; we sometimes need to collect these while
    translating array comprehension clauses and bind them later *)
module Let_binding = struct
  (** The first-class (in OCaml) type of let bindings *)
  type t =
    { let_kind   : let_kind
    ; value_kind : value_kind
    ; id         : Ident.t
    ; init       : lambda }

  (** Create a let binding *)
  let make let_kind value_kind id init =
    {let_kind; value_kind; id; init}

  (** Create a a fresh local identifier to bind (from a string), and return that
      it along with the corresponding let binding *)
  let make_id let_kind value_kind name init =
    let id = Ident.create_local name in
    id, make let_kind value_kind id init

  (** Create a a fresh local identifier to bind (from a string), and return that
      it along with the Lambda variable (with [Lvar]) for it and the
      corresponding let binding *)
  let make_id_var let_kind value_kind name init =
    let id, binding = make_id let_kind value_kind name init in
    id, Lvar id, binding

  (** Create a a fresh local identifier to bind (from a string), and return its
      corresponding Lambda variable (with [Lvar]) and let binding *)
  let make_var let_kind value_kind name init =
    let _id, var, binding = make_id_var let_kind value_kind name init in
    var, binding

  (** Create a Lambda let-binding (with [Llet]) from a first-class let
      binding *)
  let let_one {let_kind; value_kind; id; init} body =
    Llet(let_kind, value_kind, id, init, body)

  (** Create Lambda let-bindings (with [Llet]) from multiple first-class let
      bindings *)
  let let_all = List.fold_right let_one

  (** Creates a new let binding only if necessary: if the value is to be used
      (as per [usage]) [Once], then we don't need to create a binding, so we
      just return it.  However, if the value is to be reused [Many] times, then
      we create a binding with a fresh variable and return the variable (as a
      lambda term).  Thus, in an environment where the returned binding is used,
      the lambda term refers to the same value in either case. *)
  let make_if_reused (type u)
        ~(usage:u Usage.t) let_kind value_kind name value
      : lambda * (u, t) Usage.if_reused =
    match usage with
    | Once ->
        value, Used_once
    | Many ->
        let var, binding = make_var let_kind value_kind name value in
        var, Reusable binding
end

module Precompute_array_size = struct
  (** Generates the lambda expression that throws the exception once we've
      determined that precomputing the array size has overflowed.  The check for
      overflow is done elsewhere, this just throws the exception
      unconditionally. *)
  let raise_overflow_exn ~loc =
    (* CR aspectorzabusky: Is this idiomatic?  Should the argument to [string]
       (a string constant) just get [Location.none] instead? *)
    let loc' = Debuginfo.Scoped_location.to_location loc in
    let slot =
      transl_extension_path
        loc
        Env.initial_safe_string
        Predef.path_invalid_argument
    in
    (* CR aspectorzabusky: Should I call [Translprim.event_after] here?
       [Translcore.asssert_failed] does (via a local intermediary). *)
    Lprim(Praise Raise_regular,
          [Lprim(Pmakeblock(0, Immutable, None),
                 [slot; (string ~loc:loc' "Array.make")],
                  (* CR aspectorzabusky: Is "Array.make" the right argument?
                     That's not *really* what's failing... *)
                 loc)],
          loc)

  (** [safe_mul_nonneg ~loc x y] generates the lambda expression that computes
      the product [x * y] of two nonnegative integers and fails if this
      overflowed *)
  let safe_mul_nonneg ~loc x y =
    let open (val Lambda_utils.int_ops ~loc) in
    let x, x_binding =
      Let_binding.make_var Strict Pintval "x"       x
    in
    let y, y_binding =
      Let_binding.make_var Strict Pintval "y"       y
    in
    let product, product_binding =
      Let_binding.make_var Alias  Pintval "product" (x * y)
    in
    (* [x * y] is safe, for nonnegative [x] and [y], iff you can undo the
       multiplication: [(x * y)/y = x] for all nonzero [y].  We have to bind all
       the terms first to avoid extra computation. *)
    Let_binding.let_all [x_binding; y_binding; product_binding]
      (Lifthenelse(y = l0 || product / y = x,
         product,
         raise_overflow_exn ~loc))

  (** [safe_product_nonneg ~loc xs] generates the lambda expression that
      computes the product of all the lambda terms in [xs] assuming they are all
      nonnegative integers, failing if any product overflows *)
  let safe_product_nonneg ~loc = function
    | x :: xs -> List.fold_left (safe_mul_nonneg ~loc) x xs
    | []      -> int 1
      (* The empty list case can't happen with list comprehensions; we could
         raise an error here instead of returning 1 *)
end

(** This module contains the type of bindings generated when translating array
    comprehension iterators ([Typedtree.comprehension_iterator]s).  We need more
    struction than a [Let_binding.t list] because of the fixed-size array
    optimization: if we're translating an array comprehension whose size can be
    determined ahead of time, such as
    [[|x,y for x = 1 to 10 and y in some_array|]], then we need to bind more
    information so that we can reuse it to precompute the size of the target
    array.  In the example above, that means binding [1], [10], and
    [Array.length some_array], as well as remembering that the first loop
    iterates [to] instead of [downto].  We always need to bind [some_array], as
    it's indexed repeatedly, so we can't simply hide this whole type behind
    [Usage.if_reused]; we need to store some bindings all the time, and some
    bindings only in the fixed-size case.  Thus, this module, which allows you
    to work with a structured representation of the translated iterator
    bindings.  *)
module Iterator_bindings = struct
  (** This is the type of bindings generated when translating array
      comprehension iterators ([Typedtree.comprehension_iterator]).  If we are
      in the fixed-size array case, then ['u = many], and we remember all the
      information about the right-hand sides of the iterators; if not, then ['u
      = once], and we only remember a new binding for the array on the
      right-hand side of an [in] iterator, using the other terms directly. *)
  type 'u t =
    | Range of { start     : ('u, Let_binding.t)  Usage.if_reused
               ; stop      : ('u, Let_binding.t)  Usage.if_reused
               ; direction : ('u, direction_flag) Usage.if_reused }
    (** The translation of [Typedtree.Texp_comp_range], an integer iterator
        ([... = ... (down)to ...]) *)
    | Array of { iter_arr : Let_binding.t (* Always bound *)
               ; iter_len : ('u, Let_binding.t) Usage.if_reused }
    (** The translation of [Typedtree.Texp_comp_in], an array iterator
        ([... in ...]).  Note that we always remember the array ([iter_arr]), as
        it's indexed repeatedly no matter what. *)

  (** Get the [Let_binding.t]s out of a translated iterator *)
  let let_bindings = function
    | Range {start; stop; direction = _} ->
        List.concat_map Usage.list_of_reused [start; stop]
    | Array {iter_arr; iter_len} ->
        iter_arr :: Usage.list_of_reused iter_len

  (** Get the [Let_binding.t]s out of a list of translated iterators; this is
      the information we need to translate a full [for] comprehension clause
      ([Typedtree.Texp_comp_for]). *)
  let all_let_bindings bindings = List.concat_map let_bindings bindings

  (** Compute the size of a single array iterator in the fixed-size array case.
      This is either the size of a range, which itself is either
      [stop - start + 1] or [start - stop + 1] depending on if the array is
      counting up ([to]) or down ([downto]), clamped to being nonnegative; or is
      the length of the array being iterated over.  In the range case, we also
      have to check for overflow. *)
  let size ~loc : Usage.many t -> lambda = function
    | Range { start     = Reusable start
            ; stop      = Reusable stop
            ; direction = Reusable direction }
      ->
        let open (val Lambda_utils.int_ops ~loc) in
        let start = Lvar start.id in
        let stop  = Lvar stop.id in
        let low, high = match direction with
          | Upto   -> start, stop
          | Downto -> stop,  start
        in
        Lifthenelse(low <= high,
          (* The range has content *)
          (let range_size = Ident.create_local "range_size" in
           Llet(Alias, Pintval, range_size, (high - low) + l1,
             (* If the computed size of the range is nonpositive, there was
                overflow.  (The zero case is checked for when we check to see
                if the bounds are in the right order.) *)
             Lifthenelse(Lvar range_size > l0,
               Lvar range_size,
               Precompute_array_size.raise_overflow_exn ~loc))),
          (* The range is empty *)
          l0)
    | Array { iter_arr = _; iter_len = Reusable iter_len } ->
        Lvar iter_len.id

  (** Compute the total size of an array built out of a list of translated
      iterators in the fixed-size array case; since this forms a cartesian
      product, we take the product of the [size]s.  This can overflow, in which
      case we will raise an exception.  This is the operation needed to
      precompute the fixed size of a fixed-size array. *)
  let total_size ~loc (iterators : Usage.many t list) =
    Precompute_array_size.safe_product_nonneg
      ~loc
      (List.map (size ~loc) iterators)
end

(** Machinery for working with resizable arrays for the results of an array
    comprehension: they are created at a fixed, known, small size, and are
    doubled in size when necessary.  These are the arrays that back array
    comprehensions by default, but not in the fixed-size case; in that case, we
    simply construct an array of the appropriate size directly. *)
module Resizable_array = struct
  (** The starting size of a resizable array.  This is guaranteed to be a small
      power of two.  Because we resize the array by doubling, using a power of
      two means that, under the assumption that [Sys.max_array_length] is of the
      form 2^x-1, the array will only grow too large one iteration before it
      would otherwise exceed the limit.  (In practice, the program will fail by
      running out of memory first.) *)
  let starting_size = 8

  (** Create a fresh resizable array: it is mutable and has [starting_size]
      elements.  We have to provide the initial value as well as the array kind,
      thanks to the float array hack, so sometimes this will be a default value
      and sometimes it will be the first element of the comprehension *)
  let make ~loc array_kind elt =
    Lprim(Pmakearray(array_kind, Mutable),
          Misc.replicate_list elt starting_size,
          loc)

  (** Create a new array that's twice the size of the old one.  The first half
      of the array contains the same elements, and the latter half's contents
      are unspecified.  Note that this does not update [array] itself. *)
  let double ~loc array = array_append ~loc array array
  (* Implementing array doubling in by appending an array to itself may not be
     the optimal way to do array doubling, but it's good enough for now *)
end

(** Translates an iterator ([Typedtree.comprehension_iterator]), one piece of a
    [for ... and ... and ...] expression, into Lambda.  We translate iterators
    from the "outermost" iterator inwards, so this translation is done in CPS;
    the result of the translation is actually a function that's waiting for the
    body to fill into the translated loop.  The term generated by this function
    will execute the body (which is likely made of further translated iterators
    and suchlike) once for every value being iterated over, with all the
    variables bound over by the iterator available.

    This function returns both a pair of said CPSed Lambda term and the let
    bindings generated by this term (as an [Iterator_bindings.t], which see).
    The [~usage] argument controls whether the endpoints of the iteration have
    to be saved; if it is [Many], then we are dealing with the fixed-size array
    optimization, and we will generate extra bindings. *)
let iterator ~transl_exp ~scopes ~loc ~(usage : 'u Usage.t)
    : comprehension_iterator
        -> (lambda -> lambda) * 'u Iterator_bindings.t = function
  | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
      let transl_bound name bound =
        Let_binding.make_if_reused ~usage Strict Pintval
          name (transl_exp ~scopes bound)
      in
      let start, start_binding = transl_bound "start" start in
      let stop,  stop_binding  = transl_bound "stop"  stop  in
      let mk_iterator body =
        Lfor(ident, start, stop, direction, body)
      in
      mk_iterator, Range { start     = start_binding
                         ; stop      = stop_binding
                         ; direction = Usage.if_reused usage direction }
  | Texp_comp_in { pattern; sequence = iter_arr } ->
      let iter_arr_var, iter_arr_binding =
        Let_binding.make_var Strict Pgenval
          "iter_arr" (transl_exp ~scopes iter_arr)
      in
      let iter_arr_kind = Typeopt.array_kind iter_arr in
      let iter_len, iter_len_binding =
        Let_binding.make_if_reused ~usage Alias Pintval
          "iter_len"
          (Lprim(Parraylength iter_arr_kind, [iter_arr_var], loc))
      in
      let iter_ix = Ident.create_local "iter_ix" in
      let mk_iterator body =
        let open (val Lambda_utils.int_ops ~loc) in
        (* for iter_ix = 0 to Array.length iter_arr - 1 ... *)
        Lfor(iter_ix, l0, iter_len - l1, Upto,
             Matching.for_let
               ~scopes
               pattern.pat_loc
               (Lprim(Parrayrefu iter_arr_kind,
                      [iter_arr_var; Lvar iter_ix],
                      loc))
               pattern
               body)
      in
      mk_iterator, Array { iter_arr = iter_arr_binding
                         ; iter_len = iter_len_binding }

(** Translates an array comprehension binding
    ([Typedtree.comprehension_clause_binding]) into Lambda.  At parse time,
    iterators don't include patterns and bindings do; however, in the typedtree
    representation, the patterns have been moved into the iterators (so that
    range iterators can just have an [Ident.t], for translation into for loops),
    so bindings are just like iterators with a possible annotation.  As a
    result, this function is essentially the same as [iterator], which see. *)
let binding
      ~transl_exp
      ~scopes
      ~loc
      ~usage
      { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  iterator ~transl_exp ~loc ~scopes ~usage comp_cb_iterator

(** Translate the contents of a single [for ... and ...] clause (the contents of
    a [Typedtree.Texp_comp_for]) into Lambda, returning both the [lambda ->
    lambda] function awaiting the body of the translated loop, and the ['u
    Iterator_bindings.t list] containing all the bindings generated by the
    individual iterators.  This function is factored out of [clause] because it
    is also used separately in the fixed-size case. *)
let for_and_clause ~transl_exp ~scopes ~loc ~usage =
  Cps_utils.compose_map_acc (binding ~transl_exp ~loc ~scopes ~usage)

(** Translate a single clause, either [for ... and ...] or [when ...]
    ([Typedtree.comprehension_clause]), into Lambda, returning the [lambda ->
    lambda] function awaiting the body of the loop or conditional corresponding
    to this clause.  The argument to that function will be executed once for
    every tuple of elements being iterated over in the [for ... and ...] case,
    or it will be executed iff the condition is true in the [when] case.

    This function is only used if we are not in the fixed-size array case; see
    [clauses] and [for_and_clause] for more details. *)
let clause ~transl_exp ~scopes ~loc = function
  | Texp_comp_for bindings ->
      let make_clause, var_bindings =
        for_and_clause ~transl_exp ~loc ~scopes ~usage:Once bindings
      in
      fun body -> Let_binding.let_all
                    (Iterator_bindings.all_let_bindings var_bindings)
                    (make_clause body)
  | Texp_comp_when cond ->
      fun body -> Lifthenelse(transl_exp ~scopes cond, body, lambda_unit)

(** The [array_sizing] type describes whether an array comprehension has been
    translated using the fixed-size array optimization ([Fixed_size]), or it has
    not been but instead been translated using the usual dynamically-sized array
    ([Unknown_size]).

    If an array comprehension is of the form

        [|BODY for ITER and ITER ... and ITER|]

    then we can compute the size of the resulting array before allocating it
    ([Fixed_size], which carries the expression that computes this size);
    otherwise, we cannot ([Unknown_size]), and we have to dynamically grow the
    array as we iterate and shrink it to size at the end.  In this latter case,
    we need to bind the array size to a mutable variable so it can be queried,
    and [Unknown_size] carries this variable name. *)
type array_sizing =
  | Fixed_size   of lambda
  | Unknown_size of Ident.t

(** The result of translating the clauses portion of an array comprehension
    (everything but the body) *)
type translated_clauses =
  { array_sizing       : array_sizing
  (** Whether the array is of a fixed size or must be grown dynamically, and the
      attendant information; see [array_sizing] for more details. *)
  ; outer_bindings     : Let_binding.t list
  (** The bindings that must be available throughout the entire translated
      comprehension, including the definition of the initial array; these must
      come so far outside that the [Llet] forms aren't generated by the
      translation. *)
  ; make_comprehension : lambda -> lambda
  (** The translation of the comprehension's iterators, awaiting the translation
      of the comprehension's body.  All that remains to be done after this
      function is called is the creation and disposal of the array that is being
      constructed. *)
  }

(** Translate the clauses of an array comprehension (everything but the body; a
    [Typedtree.comprehension_clause list], which is the [comp_clauses] field of
    [Typedtree.comprehension]).  This function has to handle the fixed-size
    array case: if the list of clauses is a single [for ... and ...] clause,
    then the array will be preallocated at its full size and the comprehension
    will not have to resize the array (although the float array hack interferes
    with this slightly -- see [initial_array]).  In the normal case, this
    function simply wires together multiple [clause]s, and provides the variable
    holding the current array size as a binding. *)
let clauses ~transl_exp ~scopes ~loc = function
  | [Texp_comp_for bindings] ->
      let make_comprehension, var_bindings =
        for_and_clause ~transl_exp ~loc ~scopes ~usage:Many bindings
      in
      let starting_size = Iterator_bindings.total_size ~loc var_bindings in
      { array_sizing       = Fixed_size starting_size
      ; outer_bindings     = Iterator_bindings.all_let_bindings var_bindings
      ; make_comprehension }
  | clauses ->
      let array_size, array_size_binding =
        Let_binding.make_id
          Variable Pintval
          "array_size" (int Resizable_array.starting_size)
      in
      let make_comprehension =
        Cps_utils.compose_map (clause ~transl_exp ~loc ~scopes) clauses
      in
      { array_sizing       = Unknown_size array_size
      ; outer_bindings     = [array_size_binding]
      ; make_comprehension }

(** Create the initial array that will be filled by an array comprehension,
    returning both its identifier and the let binding that binds it.  The logic
    behind how to create the array is complicated, because it lies at the
    intersection of two special cases (controlled by the two non-location
    arguments to this function):

    * The float array hack means that we may not know the type of elements that
      go into this array, and so need to wait to actually create an array until
      we have seen the first element.  In this case, we have to return an empty
      array that will get overwritten later.

    * The fixed-size optimization means that we may want to preallocate the
      entire array all at once, instead of allocating a resizable array and
      growing it.

    Importantly, the two cases can co-occur, in which case later code needs to
    be aware of what has happened.

    The array that is returned is bound as a [Variable] in both the case where
    we're subject to the float array hack (i.e., [array_kind] is [Pgenarray])
    and in the case where nothing special occurs and the array is resizable; in
    the fixed-size array case, the resulting array is bound immutably, although
    it is still internally mutable.  This logic is important when translating
    comprehension bodies; see [body] for details. *)
let initial_array ~loc ~array_kind ~array_sizing =
  (* CR aspectorzabusky: I may be able to merge these two comments *)
  (* As discussed above, there are three cases to consider for how we allocate
     the array.

     1. We are subject to the float array hack: The array kind is [Pgenarray].
        In this case, we create an immutable empty array as a [Variable], since
        rather than being updated it will simply be overwritten once we have the
        first element.  This is the only time a fixed-size array needs to be a
        [Variable], since it will be overwritten on the first iteration.
     2. The array is of fixed size and known array kind, in which case we use
        [make_(float_)vect] to create the array, and bind it as [StrictOpt]
        since it never needs to be overwritten to be resized or replaced.
     3. The array is of unknown size and known array kind, in which case we
        create a small array of default values using [Pmakearray] and bind it as
        a [Variable] so that it can be overwritten when its size needs to be
        doubled. *)
  let array_let_kind, array_value = match array_sizing, array_kind with
    (* Case 1: Float array hack difficulties *)
    | (Fixed_size _ | Unknown_size _), Pgenarray ->
        Variable, Lprim(Pmakearray(Pgenarray, Immutable), [], loc)
    (* Case 2: Fixed size, known array kind *)
    | Fixed_size size, (Pintarray | Paddrarray) ->
        StrictOpt, make_vect ~loc ~length:size ~init:(int 0)
    | Fixed_size size, Pfloatarray ->
        StrictOpt, make_float_vect ~loc size
    (* Case 3: Unknown size, known array kind *)
    | Unknown_size _, (Pintarray | Paddrarray) ->
        Variable, Resizable_array.make ~loc array_kind (int 0)
    | Unknown_size _, Pfloatarray ->
        Variable, Resizable_array.make ~loc array_kind (float 0.)
  in
  Let_binding.make_id array_let_kind Pgenval "array" array_value

(** Generate the code for the body of an array comprehension.  This involves
    translating the body expression (a [Typedtree.expression], which is the
    [comp_body] field of [Typedtree.comprehension), but also handles the logic
    of filling in the array that is being produced by the comprehension.  This
    logic varies depending on whether we are subject to the float array hack or
    not and whether we are in the fixed size array case or not, so the
    correctness depends on getting the correct bindings from [initial_array] and
    [clauses]. *)
let transl_arr_body ~loc ~array_kind ~array_sizing ~array ~index ~body =
  (* The body of an array comprehension has three jobs:
       1. Compute the next element
       2. Assign it (mutably) to the next element of the array
       3. Advance the index of the next element
     However, there are several pieces of complexity:
       (a) If the array size is not fixed, we have to check if the index has
           overflowed; if it has, we have to double the size of the array.  (The
           complex case corresponds to [array_sizing] being [Unknown_size].)
       (b) If the array kind is not statically known, we initially created an
           empty array; we have to check if we're on the first iteration and use
           the putative first element of the array as the placeholder value for
           every element of the array.  (The complex case corresponds to
           [array_kind] being [Pgenarray].)
       (c) If both (a) and (b) hold, we shouldn't bother checking for an
           overflowed index on the first loop iteration.
     The result is that we build the "set the element" behavior in three steps:
       i.   First, we build the raw "set the element unconditionally" expression
            ([set_element_raw]).
       ii.  Then, if necessary, we precede that with the resizing check;
            otherwise, we leave the raw behavior alone
            ([set_element_in_bounds]).
       iii. Then, if necessary, we check to see if we're on the first iteration
            and create the fresh array instead if so; otherwise, we leave the
            size-safe behavior alone ([set_element_known_kind_in_bounds]).
       iv.  Finally, we take the resulting safe element-setting behavior (which
            could be equal to the result from any of stages i--iii), and follow
            it up by advancing the index of the element to update.
  *)
  let open (val Lambda_utils.int_ops ~loc) in
  (* CR aspectorzabusky: I used to use shadowing for the three [set_element_*]
     functions (calling them all [set_element]), but I think this is clearer? *)
  let set_element_raw elt =
    (* array.(index) <- elt *)
    Lprim(Parraysetu array_kind, [Lvar array; Lvar index; elt], loc)
      (* CR aspectorzabusky: Is [array_kind] safe here, since it could be
         [Pgenarray]?  Do we have to learn which it should be? *)
  in
  let set_element_in_bounds elt = match array_sizing with
    | Fixed_size _ ->
        set_element_raw elt
    | Unknown_size array_size ->
        Lsequence(
          (* Double the size of the array if it's time... *)
          Lifthenelse(Lvar index < Lvar array_size,
            lambda_unit,
            Lsequence(
              Lassign(array_size, i 2 * Lvar array_size),
              Lassign(array,      Resizable_array.double ~loc (Lvar array)))),
          (* ...and then set the element now that the array is big enough *)
          set_element_raw elt)
  in
  let set_element_known_kind_in_bounds = match array_kind with
    | Pgenarray ->
        let is_first_iteration = (Lvar index = l0) in
        let elt = Ident.create_local "elt" in
        let make_array = match array_sizing with
          | Fixed_size size ->
              make_vect ~loc ~length:size ~init:(Lvar elt)
          | Unknown_size _ ->
              Resizable_array.make ~loc Pgenarray (Lvar elt)
        in
        (* CR aspectorzabusky: Is Pgenval safe here? *)
        Llet(Strict, Pgenval, elt, body,
             Lifthenelse(is_first_iteration,
               Lassign(array, make_array),
               set_element_in_bounds (Lvar elt)))
    | Pintarray | Paddrarray | Pfloatarray ->
        set_element_in_bounds body
  in
  Lsequence(
    set_element_known_kind_in_bounds,
    Lassign(index, Lvar index + l1))

(** Translate an array comprehension ([Typedtree.comprehension], when it's the
    body of a [Typedtree.Texp_array_comprehension]) into Lambda.  This generates
    more efficient code in the case where the array has a known fixed size, by
    preallocating the generated array; otherwise, it dynamically resizes the
    generated array, cutting it back down to size at the end.

    The only variables this term refers to are those that come from the array
    comprehension itself; some C primitives are referenced, but no standard
    library functions. *)
let comprehension
      ~transl_exp ~scopes ~loc ~array_kind { comp_body; comp_clauses } =
  let { array_sizing; outer_bindings; make_comprehension } =
    clauses ~transl_exp ~scopes ~loc comp_clauses
  in
  let array, array_binding = initial_array ~loc ~array_kind ~array_sizing in
  let index, index_var, index_binding =
    Let_binding.make_id_var Variable Pintval "index" (int 0)
  in
  Let_binding.let_all
    (outer_bindings @ [array_binding; index_binding])
    (Lsequence(
       (* Create the array *)
       make_comprehension
         (transl_arr_body
            ~loc
            ~array_kind
            ~array_sizing
            ~array
            ~index
            ~body:(transl_exp ~scopes comp_body)),
       (* If it was dynamically grown, cut it down to size *)
       match array_sizing with
       | Fixed_size _ ->
           Lvar array
       | Unknown_size _ ->
           array_sub ~loc (Lvar array) ~offset:(int 0) ~length:index_var))
