open Lambda
open Typedtree
open Asttypes
open Transl_comprehension_utils
open Lambda_utils.Make

(** Many of the functions in this file need to translate expressions from
    Typedtree to lambda; to avoid strange dependency ordering, we parameterize
    those functions by [Translcore.transl_exp], and pass it in as a labeled
    argument, along with the necessary [scopes] labeled argument that it
    requires. *)

(* CR aspectorzabusky: I couldn't get this to build if these were run as soon as
   this file was processed *)
(** The functions that are required to build the results of list comprehensions;
    see the documentation for [CamlinternalComprehension] for more details. *)
let ( rev
    , rev_dlist_concat_map
    , rev_dlist_concat_iterate_up
    , rev_dlist_concat_iterate_down )
  =
  let transl name =
    lazy (Lambda.transl_prim "CamlinternalComprehension" name)
  in
  ( transl "rev"
  , transl "rev_dlist_concat_map"
  , transl "rev_dlist_concat_iterate_up"
  , transl "rev_dlist_concat_iterate_down" )
;;

(** The information needed to translate a single iterator from a
    [for ... and ...] clause (i.e., [x = e1 (down)to e2] or [for pat in xs]). *)
type translated_iterator =
  { builder : lambda Lazy.t
  (** The function that does the appropriate iteration (counting up, counting
      down, or iterating over a list); this function is expected to have a type
      of the form [...args... -> ('elt -> 'res rev_dlist) -> 'res rev_dlist],
      where ['a rev_dlist = 'a list -> 'a list] is the type of reversed
      difference lists, as defined in [CamlinternalComprehension]; once the
      arguments are applied (see [arg_lets]), then the function is simply
      waiting for the body of the iterator.  The use of [rev_dlist]s is for
      efficiency, as we can build things up through directly consing things on
      and then apply a single, tail-recursive reverse once we've constructed
      everything. *)
  ; arg_lets : Let_binding.t list
  (** The first-class let bindings that bind the arguments to the [builder]
      function that actually does the iteration.  These let bindings need to be
      collected separately so that they can all be bound at once before the
      whole [for ... and ...] clause, so that iterators in such a clause don't
      have their side effects performed multiple times in relation to each
      other.  Every variable bound by one of these let bindings will be passed
      to [builder], filling in the [...args...] in its type. *)
  ; element : Ident.t
  (** The name given to the values we're iterating over; needs to be a fresh
      name for [for]-[in] iterators in case the user specifies a complex
      pattern. *)
  ; element_kind : value_kind
  (** The [value_kind] of the values we're iterating over. *)
  ; add_bindings : lambda -> lambda
  (** Any extra bindings that should be present in the body of this iterator,
      for use by nested pieces of the translation; used if the user specifies a
      complex pattern in a [for]-[in] iterator. *)
  }

(** Translates an iterator ([Typedtree.comprehension_iterator]), one piece of a
    [for ... and ... and ...] expression, into Lambda.  This translation is into
    a [translated_iterator], not just a Lambda term, because the iterator
    desugars into a higher-order function which is applied to another function
    containing the body of the iteration; that body function can't be filled in
    until the rest of the translations have been done. *)
let iterator ~transl_exp ~scopes = function
  | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
      (* We have to let-bind [start] and [stop] so that they're evaluated in the
         right (i.e., left-to-right) order *)
      let transl_bound var bound =
        Let_binding.make_id' Strict Pintval var (transl_exp ~scopes bound)
      in
      let start = transl_bound "start" start in
      let stop  = transl_bound "stop"  stop  in
      { builder      = (match direction with
                        | Upto   -> rev_dlist_concat_iterate_up
                        | Downto -> rev_dlist_concat_iterate_down)
      ; arg_lets     = [start; stop]
      ; element      = ident
      ; element_kind = Pintval
      ; add_bindings = Fun.id
      }
  | Texp_comp_in { pattern; sequence } ->
      let iter_list =
        Let_binding.make_id'
          Strict Pgenval
          "iter_list" (transl_exp ~scopes sequence)
      in
      (* Create a fresh variable to use as the function argument *)
      let element = Ident.create_local "element" in
      { builder      = rev_dlist_concat_map
      ; arg_lets     = [iter_list]
      ; element
      ; element_kind = Typeopt.value_kind pattern.pat_env pattern.pat_type
      ; add_bindings =
          Matching.for_let ~scopes pattern.pat_loc (Lvar element) pattern
      }

(** Translates a list comprehension binding
    ([Typedtree.comprehension_clause_binding]) into Lambda.  At parse time,
    iterators don't include patterns and bindings do; however, in the typedtree
    representation, the patterns have been moved into the iterators (so that
    range iterators can just have an [Ident.t], for translation into for loops),
    so bindings are just like iterators with a possible annotation.  As a
    result, this function is essentially the same as [iterator], which see. *)
let binding ~transl_exp ~scopes { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  iterator ~transl_exp ~scopes comp_cb_iterator

(** Translate all the bindings of a single [for ... and ...] clause (the
    contents of a [Typedtree.Texp_comp_for]) into a pair of (1) a list of let
    bindings that are in force for the translation; and (2) a single Lambda term
    of type ['res rev_dlist], assuming we know how to translate everything that
    ought to be nested within it (the [inner_body], a function awaiting the most
    nested accumulator as a labeled argument which will produce the body of the
    iterations) and have a name for the accumulator of the current [rev_dlist]
    ([accumulator], which changes at every recursive step).  It folds together
    all the [translated_iterator]s by connecting their [body_func]tions to each
    other, and bottoms out at the [inner_body].  *)
let rec translate_bindings
          ~transl_exp ~scopes ~loc ~inner_body ~accumulator = function
  | cur_binding :: bindings ->
      let { builder; arg_lets; element; element_kind; add_bindings } =
        binding ~transl_exp ~scopes cur_binding
      in
      let inner_acc = Ident.create_local "accumulator" in
      let body_arg_lets, body =
        translate_bindings
          ~transl_exp ~scopes ~loc
          ~inner_body ~accumulator:(Lvar inner_acc) bindings
      in
      let body_func =
        Lfunction
          { kind   = Curried
          ; params = [element, element_kind; inner_acc, Pgenval]
          ; return = Pgenval
          ; attr   = default_function_attribute
          ; loc
          ; body   = add_bindings body
          }
      in
      let result =
        Lambda_utils.apply
          ~loc
          (Lazy.force builder)
          (List.map (fun Let_binding.{id; _} -> Lvar id) arg_lets @
           [body_func; accumulator])
      in
      arg_lets @ body_arg_lets, result
  | [] ->
      [], inner_body ~accumulator

(** Translate a single clause, either [for ... and ...] or [when ...]
    ([Typedtree.comprehension_clause]), into a single Lambda term of type
    ['res rev_dlist], assuming we know how to translate everything that ought to
    be nested within it (the [comprehension_body], a a function awaiting the
    most nested accumulator as a labeled argument which will produce the body of
    the iterations) and have a name for the accumulator of the current
    [rev_dlist] ([accumulator], which changes at every recursive step). *)
let rec translate_clauses
          ~transl_exp ~scopes ~loc ~comprehension_body ~accumulator = function
  | clause :: clauses ->
      let body ~accumulator =
        translate_clauses ~transl_exp ~scopes ~loc
          ~comprehension_body ~accumulator clauses
      in begin
        match clause with
        | Texp_comp_for bindings ->
            let arg_lets, bindings =
              translate_bindings
                ~transl_exp ~scopes ~loc ~inner_body:body ~accumulator bindings
            in
            Let_binding.let_all arg_lets bindings
        | Texp_comp_when cond ->
            Lifthenelse(transl_exp ~scopes cond,
                        body ~accumulator,
                        accumulator)
      end
  | [] ->
      comprehension_body ~accumulator

let comprehension ~transl_exp ~scopes ~loc { comp_body; comp_clauses } =
  let rev_comprehension =
    translate_clauses ~transl_exp ~scopes ~loc
      ~comprehension_body:(fun ~accumulator ->
        Lprim(
          (* ( :: ) *)
          Pmakeblock(0, Immutable, None),
          [transl_exp ~scopes comp_body; accumulator],
          loc))
      ~accumulator:(int 0 (* Actually [[]], the empty list *))
      comp_clauses
  in
  Lambda_utils.apply ~loc (Lazy.force rev) [rev_comprehension]
