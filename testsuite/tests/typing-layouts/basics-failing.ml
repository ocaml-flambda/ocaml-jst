(* TEST
   * expect
*)

(* XXX layouts: merge with basics.ml once this passes *)

(* Test 16: Inferred a value layout for a recursive unboxed type *)

(* XXX layouts: if we decide *not* to infer a value layout for these,
   update the pretty-printer to always print a user-written layout for
   an unboxed type *)
type loopy = MkL of loopy [@@unboxed]
type loopy2 = { f : loopy2 } [@@unboxed]

[%%expect{|
success with value layouts
|}]
