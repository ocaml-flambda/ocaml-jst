module Comprehensions : sig
  type iterator =
    | Range of { start     : Parsetree.expression
               ; stop      : Parsetree.expression
               ; direction : Asttypes.direction_flag }
        (** "= START to STOP" (direction = Upto)
            "= START downto STOP" (direction = Downto) *)
    | In of Parsetree.expression
      (** "in EXPR" *)

  type clause_binding =
    { pattern    : Parsetree.pattern
    ; iterator   : iterator
    ; attributes : Parsetree.attribute list }
    (** PAT (in/= ...) [@...] *)

  type clause =
    | For of clause_binding list
        (** "for PAT (in/= ...) and PAT (in/= ...) and ..."; must be nonempty *)
    | When of Parsetree.expression
        (** "when EXPR" *)

  type comprehension =
    { body : Parsetree.expression
        (** The body/generator of the comprehension *)
    ; clauses : clause list
        (** The clauses of the comprehension; must be nonempty *) }

  type comprehension_expr =
    | Cexp_list_comprehension  of comprehension
        (** [BODY ...CLAUSES...] *)
    | Cexp_array_comprehension of comprehension
        (** [|BODY ...CLAUSES...|] *)

  val expr_of_comprehension_expr :
    loc:Location.t -> comprehension_expr -> Parsetree.expression

  val comprehension_expr_of_expr : Parsetree.expression -> comprehension_expr
end

type extension_expr =
  | Eexp_comprehension of Comprehensions.comprehension_expr

val extension_expr_of_expr :
  Parsetree.expression -> extension_expr option

val expr_of_extension_expr :
  loc:Location.t -> Clflags.extension -> extension_expr -> Parsetree.expression

type extension =
  | Extension :
      { expr_of : loc:Location.t -> 'a -> Parsetree.expression
      ; of_expr : Parsetree.expression -> 'a
      ; wrap    : 'a -> extension_expr
      ; unwrap  : extension_expr -> 'a option }
    -> extension

val extension : Clflags.extension -> extension

(** Matches expressions of the form

        ([%extension.NAME] BODY)

    and returns [Some (NAME, BODY)] if successful, where NAME is a list of
    dot-separated name components.  If the expression is not an application
    headed by an extension node whose name begins with ["extension."], returns
    [None].  If the expression is a malformed extension application, raises an
    [Error].  Malformed means either:

    1. The [[%extension.NAME]] extension point has a payload; extensions must be
       empty, so other ppxes can traverse "into" them.

    2. The [[%extension.NAME]] extension point is applied to something other
       than a single unlabeled argument.

    The second requirement may be loosened in the future. *)
val expand_extension_expr :
  Parsetree.expression -> (string list * Parsetree.expression) option
