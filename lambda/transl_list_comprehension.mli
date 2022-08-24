open Lambda
open Typedtree
open Debuginfo.Scoped_location

(** Translate list comprehensions; see the .ml file for more details *)

(** Translate a list comprehension ([Typedtree.comprehension], when it's the
    body of a [Typedtree.Texp_list_comprehension]) into Lambda.

    The only variables this term refers to are those from
    [CamlinternalComprehension] and those that come from the array comprehension
    itself; we also rely on the structure of the [list] type.

    This function needs to translate expressions from Typedtree into Lambda, and
    so is parameterized by [Translcore.transl_exp], its [scopes] argument, and
    the [loc]ation. *)
val comprehension
  :  transl_exp:(scopes:scopes -> expression -> lambda)
  -> scopes:scopes
  -> loc:scoped_location
  -> comprehension
  -> lambda
