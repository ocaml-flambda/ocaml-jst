open Lambda
open Typedtree
open Debuginfo.Scoped_location

val comprehension
  :  transl_exp:(scopes:scopes -> expression -> lambda)
  -> scopes:scopes
  -> loc:scoped_location
  -> array_kind:array_kind
  -> comprehension
  -> lambda
