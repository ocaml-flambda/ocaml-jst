(* TEST
   ocamlc_byte_exit_status = "2"
   * setup-ocamlc.byte-build-env
   ** ocamlc.byte
   *** check-ocamlc.byte-output
*)

(* What happens if the user tries to write one of the ocaml-jst extensions in
   terms of extension nodes but messes up?  In practice we don't expect to ever
   see these errors, but one never knows (and a bug in our desugaring could
   cause them).  The let-binding is named after the constructor in
   [extensions.ml] representing this particular error. *)

(* We cannot use an expect-test here, because these are essentially parsing
   errors. The expect-test infrastructure uses Ast_mapper to prepare its
   input, and the call to Ast_mapper fails with a bogus extension setup,
   because it tries to decode extensions. *)

let _unknown_extension = [%extension.this_extension_doesn't_exist] ();;

(*
Line 1, characters 25-69:
1 | let _unknown_extension = [%extension.this_extension_doesn't_exist] ();;
                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Unknown extension "this_extension_doesn't_exist" referenced via an [%extension.this_extension_doesn't_exist] extension node
*)

