open Lambda
open Typedtree
open Asttypes

(* CR aspectorzabusky: Needs to be factored out properly so this module doesn't
   have to depend on [Transl_array_comprehension] *)
module Cps_utils = Transl_array_comprehension.Cps_utils

(* CR aspectorzabusky: Needs to be factored out properly so this module doesn't
   have to depend on [Transl_array_comprehension] *)
open Transl_array_comprehension.Lambda_utils.Make

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

type comprehension_chunk_data =
  { accumulator : lambda ; make_body : lambda -> lambda }

let iterator ~transl_exp ~scopes ~loc iterator =
  let inner_acc = Ident.create_local "accumulator" in
  let make_iterator
        ~builder ~builder_args ~element ~element_kind ~make_body next =
    let iteration body =
      let body_func =
        Lfunction { kind   = Curried
                  ; params = [element, element_kind ; inner_acc, Pgenval]
                  ; return = Pgenval
                  ; attr   = default_function_attribute
                  ; loc    = loc
                  ; body   = make_body (next.make_body body)
                  }
      in
      Lapply { ap_loc         = loc
             ; ap_func        = Lazy.force builder
             ; ap_args        = body_func :: (builder_args @ [next.accumulator])
             ; ap_tailcall    = Default_tailcall
             ; ap_inlined     = Default_inlined
             ; ap_specialised = Default_specialise
             ; ap_probe       = None
             }
    in
    { accumulator = Lvar inner_acc; make_body = iteration }
  in
  match iterator with
  | Texp_comp_range { ident; pattern = _; start; stop; direction } ->
      make_iterator
        ~builder:(match direction with
          | Upto   -> rev_dlist_concat_iterate_up
          | Downto -> rev_dlist_concat_iterate_down)
        ~builder_args:(List.map (transl_exp ~scopes) [start; stop])
        ~element:ident
        ~element_kind:Pintval
        ~make_body:Fun.id
  | Texp_comp_in { pattern; sequence } ->
      let element = Ident.create_local "element" in
      make_iterator
        ~builder:rev_dlist_concat_map
        ~builder_args:[transl_exp ~scopes sequence]
        ~element
        ~element_kind:(Typeopt.value_kind pattern.pat_env pattern.pat_type)
        ~make_body:
          (Matching.for_let ~scopes pattern.pat_loc (Lvar element) pattern)

let binding
      ~transl_exp
      ~scopes
      ~loc
      { comp_cb_iterator; comp_cb_attributes = _ } =
  (* CR aspectorzabusky: What do we do with attributes here? *)
  iterator ~transl_exp ~loc ~scopes comp_cb_iterator

let clause ~transl_exp ~scopes ~loc = function
  | Texp_comp_for bindings ->
      Cps_utils.compose_map (binding ~transl_exp ~loc ~scopes) bindings
  | Texp_comp_when cond ->
      fun { accumulator; make_body } ->
        { accumulator
        ; make_body = fun body ->
            Lifthenelse(transl_exp ~scopes cond, make_body body, accumulator) }

let comprehension ~transl_exp ~scopes ~loc { comp_body; comp_clauses } =
  let { accumulator = innermost_acc; make_body = make_comprehension } =
    Cps_utils.compose_map
      (clause ~transl_exp ~scopes ~loc)
      comp_clauses
      { accumulator = int 0 (* Actually [[]], the empty list *)
      ; make_body   = fun innermost_acc ->
          Lprim(
            (* ( :: ) *)
            Pmakeblock(0, Immutable, None),
            [(transl_exp ~scopes comp_body); innermost_acc],
            loc)
      }
  in
  Lapply { ap_loc         = loc
         ; ap_func        = Lazy.force rev
         ; ap_args        = [make_comprehension innermost_acc]
         ; ap_tailcall    = Default_tailcall
         ; ap_inlined     = Default_inlined
         ; ap_specialised = Default_specialise
         ; ap_probe       = None
         }
