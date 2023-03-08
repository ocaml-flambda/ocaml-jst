(** Syntax for our custom ocaml-jst language extensions.  This module provides
    two things:

    1. First-class ASTs for all syntax introduced by our language extensions,
       one for each OCaml AST we extend, divided up into one extension per
       module and all available at once through modules named after the
       syntactic category ([Expression.t], etc.).

    2. A way to interpret these values as terms of the coresponding OCaml ASTs,
       and to match on terms of those OCaml ASTs to see if they're language
       extension terms.

    We keep our language extensions separate so that we can avoid having to
    modify the existing AST, as this would break compatibility with every
    existing ppx.

    For details on the rationale behind this approach (and for some of the gory
    details), see [Extensions_parsing]. *)

(*********************************************)
(* Individual extensions *)

(** The ASTs for list and array comprehensions *)
module Comprehensions : sig
  type iterator =
    | Range of { start     : Parsetree.expression
               ; stop      : Parsetree.expression
               ; direction : Asttypes.direction_flag }
    (** "= START to STOP" (direction = Upto)
        "= START downto STOP" (direction = Downto) *)
    | In of Parsetree.expression
    (** "in EXPR" *)

  (* In [Typedtree], the [pattern] moves into the [iterator]. *)
  type clause_binding =
    { pattern    : Parsetree.pattern
    ; iterator   : iterator
    ; attributes : Parsetree.attribute list }
    (** PAT (in/=) ... [@...] *)

  type clause =
    | For of clause_binding list
    (** "for PAT (in/=) ... and PAT (in/=) ... and ..."; must be nonempty *)
    | When of Parsetree.expression
    (** "when EXPR" *)

  type comprehension =
    { body : Parsetree.expression
    (** The body/generator of the comprehension *)
    ; clauses : clause list
    (** The clauses of the comprehension; must be nonempty *) }

  type expression =
    | Cexp_list_comprehension  of comprehension
    (** [BODY ...CLAUSES...] *)
    | Cexp_array_comprehension of Asttypes.mutable_flag * comprehension
    (** [|BODY ...CLAUSES...|] (flag = Mutable)
        [:BODY ...CLAUSES...:] (flag = Immutable)
          (only allowed with [-extension immutable_arrays]) *)

  val expr_of : loc:Location.t -> expression -> Parsetree.expression_desc
end

(** The ASTs for immutable arrays.  When we merge this upstream, we'll merge
    these into the existing [P{exp,pat}_array] constructors by adding a
    [mutable_flag] argument (just as we did with [T{exp,pat}_array]). *)
module Immutable_arrays : sig
  type expression =
    | Iaexp_immutable_array of Parsetree.expression list
    (** [: E1; ...; En :] *)
    (* CR aspectorzabusky: Or [Iaexp_iarray]? *)

  type pattern =
    | Iapat_immutable_array of Parsetree.pattern list
    (** [: P1; ...; Pn :] **)
    (* CR aspectorzabusky: Or [Iapat_iarray]? *)

  val expr_of : loc:Location.t -> expression -> Parsetree.expression_desc
  val pat_of : loc:Location.t -> pattern -> Parsetree.pattern_desc
end

(******************************************)
(* Individual syntactic categories *)

(** Language extensions in expressions *)
module Expression : sig
  type t =
    | Eexp_comprehension   of Comprehensions.expression
    | Eexp_immutable_array of Immutable_arrays.expression

  include Extended_AST with type t := t
                        and type ast := Parsetree.expression
                        and type ast_desc := Parsetree.expression_desc
end

(** Language extensions in patterns *)
module Pattern : sig
  type t =
    | Epat_immutable_array of Immutable_arrays.pattern

  include Extended_AST with type t := t
                        and type ast := Parsetree.pattern
                        and type ast_desc := Parsetree.pattern_desc
end
