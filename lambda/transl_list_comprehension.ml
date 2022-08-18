open Lambda
open Typedtree
open Asttypes
open Transl_comprehension_utils
open Lambda_utils.Make

(* CR aspectorzabusky: I couldn't get this to build if these were run as soon as
   this file was processed *)
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

type translated_iterator =
  { builder : lambda Lazy.t
  ; builder_args : expression list
  ; element : Ident.t
  ; element_kind : value_kind
  ; add_bindings : lambda -> lambda
  }

let iterator ~scopes = function
  | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
      { builder      = (match direction with
          | Upto   -> rev_dlist_concat_iterate_up
          | Downto -> rev_dlist_concat_iterate_down)
      ; builder_args = [start; stop]
      ; element      = ident
      ; element_kind = Pintval
      ; add_bindings = Fun.id
      }
  | Texp_comp_in { pattern; sequence } ->
      (* Create a fresh variable to use as the function argument *)
      let element      = Ident.create_local "element" in
      { builder      = rev_dlist_concat_map
      ; builder_args = [sequence]
      ; element
      ; element_kind = Typeopt.value_kind pattern.pat_env pattern.pat_type
      ; add_bindings =
          Matching.for_let ~scopes pattern.pat_loc (Lvar element) pattern
      }

let binding ~scopes { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  iterator ~scopes comp_cb_iterator

let rec translate_bindings
          ~transl_exp ~scopes ~loc ~inner_body ~accumulator = function
  | cur_binding :: bindings ->
      let { builder ; builder_args ; element ; element_kind ; add_bindings } =
        binding ~scopes cur_binding
      in
      let body_func =
        let inner_acc = Ident.create_local "accumulator" in
        Lfunction
          { kind   = Curried
          ; params = [element, element_kind; inner_acc, Pgenval]
          ; return = Pgenval
          ; attr   = default_function_attribute
          ; loc
          ; body   =
              add_bindings
                (translate_bindings
                   ~transl_exp ~scopes ~loc
                   ~inner_body ~accumulator:(Lvar inner_acc) bindings)
          }
      in
      let args =
        body_func ::
        (List.map (transl_exp ~scopes) builder_args @
         [accumulator])
      in
      Lambda_utils.apply ~loc (Lazy.force builder) args
  | [] ->
      inner_body ~accumulator

let rec translate_clauses
          ~transl_exp ~scopes ~loc ~comprehension_body ~accumulator = function
  | clause :: clauses ->
      let body ~accumulator =
        translate_clauses ~transl_exp ~scopes ~loc
          ~comprehension_body ~accumulator clauses
      in begin
        match clause with
        | Texp_comp_for bindings ->
            translate_bindings
              ~transl_exp ~scopes ~loc ~inner_body:body ~accumulator bindings
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
