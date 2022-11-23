(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                         Alain Frisch, LexiFi                           *)
(*                                                                        *)
(*   Copyright 2012 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Support for some of the builtin attributes

    - ocaml.deprecated
    - ocaml.alert
    - ocaml.error
    - ocaml.ppwarning
    - ocaml.warning
    - ocaml.warnerror
    - ocaml.explicit_arity (for camlp4/camlp5)
    - ocaml.warn_on_literal_pattern
    - ocaml.deprecated_mutable
    - ocaml.boxed / ocaml.unboxed
    - ocaml.nolabels
    - ocaml.inline
    - ocaml.afl_inst_ratio
    - ocaml.flambda_o3
    - ocaml.flambda_oclassic
    - layout attributes:
      - ocaml.any
      - ocaml.value
      - ocaml.void
      - ocaml.immediate
      - ocaml.immediate64

    {b Warning:} this module is unstable and part of
  {{!Compiler_libs}compiler-libs}.

*)

val check_alerts: Location.t -> Parsetree.attributes -> string -> unit
val check_alerts_inclusion:
  def:Location.t -> use:Location.t -> Location.t -> Parsetree.attributes ->
  Parsetree.attributes -> string -> unit
val alerts_of_attrs: Parsetree.attributes -> Misc.alerts
val alerts_of_sig: Parsetree.signature -> Misc.alerts
val alerts_of_str: Parsetree.structure -> Misc.alerts

val check_deprecated_mutable:
    Location.t -> Parsetree.attributes -> string -> unit
val check_deprecated_mutable_inclusion:
  def:Location.t -> use:Location.t -> Location.t -> Parsetree.attributes ->
  Parsetree.attributes -> string -> unit

val check_no_alert: Parsetree.attributes -> unit

val error_of_extension: Parsetree.extension -> Location.error

val warning_attribute: ?ppwarning:bool -> Parsetree.attribute -> unit
  (** Apply warning settings from the specified attribute.
      "ocaml.warning"/"ocaml.warnerror" (and variants without the prefix)
      are processed and other attributes are ignored.

      Also implement ocaml.ppwarning (unless ~ppwarning:false is
      passed).
  *)

val warning_scope:
  ?ppwarning:bool ->
  Parsetree.attributes -> (unit -> 'a) -> 'a
  (** Execute a function in a new scope for warning settings.  This
      means that the effect of any call to [warning_attribute] during
      the execution of this function will be discarded after
      execution.

      The function also takes a list of attributes which are processed
      with [warning_attribute] in the fresh scope before the function
      is executed.
  *)

val warn_on_literal_pattern: Parsetree.attributes -> bool
val explicit_arity: Parsetree.attributes -> bool

val layout: Parsetree.attributes -> Asttypes.layout_annotation option

val has_unboxed: Parsetree.attributes -> bool
val has_boxed: Parsetree.attributes -> bool

val parse_standard_interface_attributes : Parsetree.attribute -> unit
val parse_standard_implementation_attributes : Parsetree.attribute -> unit

val has_local_opt: Parsetree.attributes -> bool
val has_curry: Parsetree.attributes -> bool
val has_global: Parsetree.attributes -> bool
val has_nonlocal: Parsetree.attributes -> bool

(* These functions report Error if the builtin extension.* attributes
   are present despite the extension being disabled *)
val has_local: Parsetree.attributes -> (bool,unit) result
val tailcall : Parsetree.attributes -> ([`Tail|`Nontail] option, [`Conflict]) result
val has_include_functor : Parsetree.attributes -> (bool,unit) result

