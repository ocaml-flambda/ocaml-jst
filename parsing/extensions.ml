open Parsetree

type malformed_extension =
  | Has_payload of payload
  | Wrong_arguments of (Asttypes.arg_label * expression) list

type error =
  | Malformed_extension of string list * malformed_extension
  | Unknown_extension of string
  | Disabled_extension of Clflags.extension
  | Unnamed_extension
  | Bad_introduction of string * string list

exception Error of Location.t * error

let report_error ~loc = function
  | Malformed_extension(name, malformed) -> begin
      let name = String.concat "." ("extension" :: name) in
      match malformed with
      | Has_payload _payload ->
          Location.errorf
            ~loc
            "Extension extension nodes are not allowed to have a payload, \
             but \"%s\" does"
          name
      | Wrong_arguments arguments ->
          Location.errorf
            ~loc
            "Extension extension nodes must be applied to exactly one \
             unlabeled argument, but \"%s\" was applied to %s"
            name
            (match arguments with
             | [Labelled _, _] -> "a labeled argument"
             | [Optional _, _] -> "an optional argument"
             | _ -> Int.to_string (List.length arguments) ^ " arguments")
    end
  | Unknown_extension name ->
      Location.errorf
        ~loc
        "Unknown extension \"%s\" referenced via an [%%extension.%s] \
         extension node"
        name
        name
  | Disabled_extension ext ->
      Location.errorf
        ~loc
        "The extension \"%s\" is disabled and cannot be used"
        (Clflags.string_of_extension ext)
  | Unnamed_extension ->
      Location.errorf
        ~loc
        "Cannot have an extension node named [%%extension]"
  | Bad_introduction(name, subnames) ->
      Location.errorf
        ~loc
        "The extension \"%s\" was referenced improperly; it started with an \
         [%%extension.%s] extension node, not an [%%extension.%s] one"
        name
        (String.concat "." (name :: subnames))
        name

let () =
  Location.register_error_of_exn
    (function
      | Error(loc, err) -> Some (report_error ~loc err)
      | _ -> None)

let extension_tag ~loc names =
  Ast_helper.Exp.extension
    ~loc
    ({ txt = String.concat "." ("extension" :: names); loc }, PStr [])

let extension_expr ~loc names expr =
  Ast_helper.Exp.apply ~loc (extension_tag ~loc names) [Nolabel, expr]

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
let expand_extension_expr expr =
  match expr.pexp_desc with
  | Pexp_apply
      ( { pexp_desc =
            Pexp_extension
              ( { txt = ext_name; loc = ext_loc }
              , ext_payload )
        ; _ }
      , arguments ) ->
    begin
      match String.split_on_char '.' ext_name with
      | "extension" :: names -> begin
          let raise_malformed err =
            raise (Error(ext_loc, Malformed_extension(names, err)))
          in
          match ext_payload with
          | PStr [] -> begin
              match arguments with
              | [Nolabel, body] -> Some (names, body)
              | _ -> raise_malformed (Wrong_arguments arguments)
            end
          | _ -> raise_malformed (Has_payload ext_payload)
        end
      | _ -> None
    end
  | _ -> None

module Comprehensions = struct
  type iterator =
    | Range of { start     : expression
               ; stop      : expression
               ; direction : Asttypes.direction_flag }
        (** "= START to STOP" (direction = Upto)
            "= START downto STOP" (direction = Downto) *)
    | In of expression
      (** "in EXPR" *)

  type clause_binding =
    { pattern    : pattern
    ; iterator   : iterator
    ; attributes : attribute list }
    (** PAT (in/= ...) [@...] *)

  type clause =
    | For of clause_binding list
        (** "for PAT (in/= ...) and PAT (in/= ...) and ..."; must be nonempty *)
    | When of expression
        (** "when EXPR" *)

  type comprehension =
    { body    : expression
        (** The body/generator of the comprehension *)
    ; clauses : clause list
        (** The clauses of the comprehension; must be nonempty *) }

  type comprehension_expr =
    | Cexp_list_comprehension  of comprehension
        (** [BODY ...CLAUSES...] *)
    | Cexp_array_comprehension of comprehension
        (** [|BODY ...CLAUSES...|] *)

  let extension_name = Clflags.string_of_extension Comprehensions

  (* CR aspectorzabusky: new name? *)
  let comprehension_expr ~loc names =
    extension_expr ~loc (extension_name :: names)

  let expr_of_iterator ~loc = function
    | Range { start; stop; direction } ->
        comprehension_expr
          ~loc
          [ "for"
          ; "range"
          ; match direction with
            | Upto   -> "upto"
            | Downto -> "downto" ]
          (Ast_helper.Exp.tuple [start; stop])
    | In seq ->
        comprehension_expr ~loc ["for"; "in"] seq

  let expr_of_clause_binding ~loc { pattern; iterator; attributes } =
    Ast_helper.Vb.mk
      ~loc
      ~attrs:attributes
      pattern
      (expr_of_iterator ~loc iterator)

  let expr_of_clause ~loc = function
    | For iterators -> fun rest ->
        comprehension_expr
          ~loc
          ["for"]
          (Ast_helper.Exp.let_
             Nonrecursive
             (List.map (expr_of_clause_binding ~loc) iterators)
             rest)
    | When cond -> fun rest ->
        comprehension_expr
          ~loc
          ["when"]
          (Ast_helper.Exp.sequence cond rest)

  let expr_of_comprehension ~loc ~type_ { body; clauses } =
    comprehension_expr
      ~loc
      [type_]
      (List.fold_right
         (expr_of_clause ~loc)
         clauses
         (comprehension_expr ~loc ["body"] body))

  let expr_of_comprehension_expr ~loc eexpr =
    let ghost_loc = { loc with Location.loc_ghost = true } in
    let expr_of_comprehension_type type_ comp =
      comprehension_expr ~loc [] (expr_of_comprehension ~loc:ghost_loc ~type_ comp)
    in
    match eexpr with
    | Cexp_list_comprehension  comp -> expr_of_comprehension_type "list"  comp
    | Cexp_array_comprehension comp -> expr_of_comprehension_type "array" comp

  let expand_comprehension_extension_expr expr =
    match expand_extension_expr expr with
    | Some (comprehensions :: name, expr)
      when String.equal comprehensions extension_name ->
        name, expr
    | Some (name, _) ->
        failwith ("Tried to desugar the non-comprehension extension point \
                   \"extension." ^ String.concat "." name ^ "\" as part of a \
                   comprehension expression")
    | None ->
        failwith "Tried to desugar a non-extension expression as part of a \
                  comprehension expression"

  let expand_comprehension_extension_expr_failure name =
    failwith ("Unknown, unexpected, or malformed comprehension extension point \
               \"extension.comprehension." ^ String.concat "." name ^ "\"")

  let iterator_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["for"; "range"; "upto"],
      { pexp_desc = Pexp_tuple [start; stop]; _ } ->
      (* CR aspectorzabusky: Check other parts of the [pexp_desc]? *)
        Range { start; stop; direction = Upto }
    | ["for"; "range"; "downto"],
      { pexp_desc = Pexp_tuple [start; stop]; _ } ->
      (* CR aspectorzabusky: Check other parts of the [pexp_desc]? *)
        Range { start; stop; direction = Downto }
    | ["for"; "in"], seq ->
        In seq
    | bad, _ ->
        expand_comprehension_extension_expr_failure bad

  let clause_binding_of_vb { pvb_pat; pvb_expr; pvb_attributes; pvb_loc = _ } =
    { pattern = pvb_pat
    ; iterator = iterator_of_expr pvb_expr
    ; attributes = pvb_attributes }

  let add_clause clause comp = { comp with clauses = clause :: comp.clauses }

  let rec raw_comprehension_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["for"], { pexp_desc = Pexp_let(Nonrecursive, iterators, rest); _ } ->
        add_clause
          (For (List.map clause_binding_of_vb iterators))
          (raw_comprehension_of_expr rest)
    | ["when"], { pexp_desc = Pexp_sequence(cond, rest); _ } ->
        add_clause
          (When cond)
          (raw_comprehension_of_expr rest)
    | ["body"], body ->
        { body; clauses = [] }
    | bad, _ ->
        expand_comprehension_extension_expr_failure bad

  let comprehension_of_expr expr =
    match raw_comprehension_of_expr expr with
    | { body = _; clauses = [] } ->
        failwith "Tried to desugar a comprehension with no clauses"
    | comp -> comp

  let comprehension_expr_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["list"], comp ->
        Cexp_list_comprehension (comprehension_of_expr comp)
    | ["array"], comp ->
        Cexp_array_comprehension (comprehension_of_expr comp)
    | bad, _ ->
        expand_comprehension_extension_expr_failure bad
end

type extension_expr =
  | Eexp_comprehension of Comprehensions.comprehension_expr

type extension =
  | Extension :
      { expr_of : loc:Location.t -> 'a -> Parsetree.expression
      ; of_expr : Parsetree.expression -> 'a
      ; wrap    : 'a -> extension_expr
      ; unwrap  : extension_expr -> 'a option }
    -> extension

let extension : Clflags.extension -> extension = function
  | Comprehensions ->
      Extension { expr_of = Comprehensions.expr_of_comprehension_expr
                ; of_expr = Comprehensions.comprehension_expr_of_expr
                ; wrap    = (fun cexp -> Eexp_comprehension cexp)
                ; unwrap  = (function | Eexp_comprehension cexp -> Some cexp
                                      (*| _                       -> None*)) }

let extension_expr_of_expr expr =
  let raise_error err = raise (Error (expr.pexp_loc, err)) in
  match expand_extension_expr expr with
  | None -> None
  | Some ([name], expr) -> begin
      match Clflags.extension_of_string name with
      | Some ext ->
          if Clflags.is_extension_enabled ext
          then
            let Extension ext = extension ext in
            Some (ext.wrap (ext.of_expr expr))
          else
            raise_error (Disabled_extension ext)
      | _ -> raise_error (Unknown_extension name)
    end
  | Some ([], _) ->
      raise_error Unnamed_extension
  | Some (name :: subnames, _) ->
      raise_error (Bad_introduction(name, subnames))

(* CR aspectorzabusky: Is this really the right API? *)
let expr_of_extension_expr ~loc extn eexpr =
  if Clflags.is_extension_enabled extn
  then
    let Extension ext = extension extn in
    match ext.unwrap eexpr with
    | Some eexpr' -> ext.expr_of ~loc eexpr'
    | None ->
        failwith
          (Printf.sprintf
             "Wrong extension expression for the extension \"%s\""
             (Clflags.string_of_extension extn))
  else
    failwith
      (Printf.sprintf
         "The extension \"%s\" is not enabled\""
         (Clflags.string_of_extension extn))
