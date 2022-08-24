open Lambda
open Typedtree
open Debuginfo.Scoped_location

(** Translate array comprehensions; see the .ml file for more details *)

(** Translate an array comprehension ([Typedtree.comprehension], when it's the
    body of a [Typedtree.Texp_array_comprehension]) into Lambda.  This generates
    more efficient code in the case where the array has a known fixed size, by
    preallocating the generated array; otherwise, it dynamically resizes the
    generated array, cutting it back down to size at the end.

    The only variables this term refers to are those that come from the array
    comprehension itself; some C primitives are referenced, but no standard
    library functions. *)
val comprehension
  :  transl_exp:(scopes:scopes -> expression -> lambda)
  -> scopes:scopes
  -> loc:scoped_location
  -> array_kind:array_kind
  -> comprehension
  -> lambda
