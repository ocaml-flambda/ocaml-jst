(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Jeremie Dimino, Jane Street Europe                   *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Types

type t = layout

module Const = struct
  type t = Asttypes.const_layout

  let constrain_default_void = Layout.get_defaulting ~default:Sort.Void
  let can_make_void l = Asttypes.Void = constrain_default_void l
end

let of_const_layout_opt annot_opt ~default =
  match annot_opt with
  | None -> default
  | Some {Location.txt = annot} -> Layout.of_const annot

let of_attributes ~default attrs =
  of_const_layout_opt ~default (Builtin_attributes.layout attrs)

let to_string lay = match Layout.get lay with
  | Const c -> Pprintast.const_layout_to_string c
  | Var _ -> "<sort variable>"

let format ppf t = Format.fprintf ppf "%s" (to_string t)

module Violation = struct
  type nonrec t =
    | Not_a_sublayout of t * t
    | No_intersection of t * t

  let report_with_offender ~offender ppf t =
    let pr fmt = Format.fprintf ppf fmt in
    match t with
    | Not_a_sublayout (l1, l2) ->
        pr "%t has layout %a, which is not a sublayout of %a." offender
          format l1 format l2
    | No_intersection (l1, l2) ->
        pr "%t has layout %a, which does not overlap with %a." offender
          format l1 format l2

  let report_with_offender_sort ~offender ppf t =
    let sort_expected =
      "A representable layout was expected, but"
    in
    let pr fmt = Format.fprintf ppf fmt in
    match t with
    | Not_a_sublayout (l1, l2) ->
      pr "%s@ %t has layout %a, which is not a sublayout of %a."
        sort_expected offender format l1 format l2
    | No_intersection (l1, l2) ->
      pr "%s@ %t has layout %a, which does not overlap with %a."
        sort_expected offender format l1 format l2

  let report_with_name ~name ppf t =
    let pr fmt = Format.fprintf ppf fmt in
    match t with
    | Not_a_sublayout (l1,l2) ->
        pr "%s has layout %a, which is not a sublayout of %a." name
          format l1 format l2
    | No_intersection (l1, l2) ->
        pr "%s has layout %a, which does not overlap with %a." name
          format l1 format l2
end

let all_void layouts =
  Array.for_all (fun l ->
    match Layout.get l with
    | Const Void -> true
    | Const (Any | Immediate | Immediate64 | Value) | Var _ -> false)
    layouts

(* CR layouts: this function is suspect; it seems likely to reisenberg
   that refactoring could get rid of it *)
let sort_of_layout l =
  match Layout.get l with
  | Const Void -> Sort.void
  | Const (Value | Immediate | Immediate64) -> Sort.value
  | Const Any -> Misc.fatal_error "Type_layout.sort_of_layout"
  | Var v -> Sort.of_var v

let layout_bound_of_record_representation = function
  | Record_unboxed l -> l
  | Record_float -> Layout.value
  | Record_inlined (tag,rep) -> begin
      match (tag,rep) with
      | Extension _, _ -> Layout.value
      | _, Variant_extensible -> Layout.value
      | Ordinary _, Variant_unboxed l -> l (* n must be 0 here *)
      | Ordinary {src_index}, Variant_boxed layouts ->
        if all_void layouts.(src_index) then Layout.immediate else Layout.value
    end
  | Record_boxed layouts when all_void layouts -> Layout.immediate
  | Record_boxed _ -> Layout.value

let cstr_layouts_immediate layouts = Array.for_all all_void layouts

let layout_bound_of_variant_representation = function
    Variant_unboxed l -> l
  | Variant_boxed layouts ->
    if cstr_layouts_immediate layouts then Layout.immediate else Layout.value
  | Variant_extensible -> Layout.value

(* should not mutate sorts *)
let layout_bound_of_kind = function
  | Type_abstract { layout } -> layout
  | Type_open -> Layout.value
  | Type_record (_,rep) -> layout_bound_of_record_representation rep
  | Type_variant (_, rep) -> layout_bound_of_variant_representation rep

let default_to_value t =
  ignore (Layout.get_defaulting ~default:Value t)

let intersection l1 l2 =
  let err = Error (Violation.No_intersection (l1, l2)) in
  let equality_check is_eq l = if is_eq then Ok l else err in
  (* it's OK not to cache the result of [get], because [get] does path
     compression *)
  match Layout.get l1, Layout.get l2 with
  | Const Any, _ -> Ok l2
  | _, Const Any -> Ok l1
  | Const c1, Const c2 when Layout.equal_const c1 c2 -> Ok l1
  | Const (Immediate64 | Immediate), Const (Immediate64 | Immediate) ->
    Ok Layout.immediate
  | Const ((Immediate64 | Immediate) as imm), l
  | l, Const ((Immediate64 | Immediate) as imm) ->
    equality_check (Layout.equate (Layout.of_get_result l) Layout.value)
      (Layout.of_const imm)
  | _, _ -> equality_check (Layout.equate l1 l2) l1

let sublayout sub super =
  let ok = Ok sub in
  let err = Error (Violation.Not_a_sublayout (sub,super)) in
  let equality_check is_eq = if is_eq then ok else err in
  match Layout.get sub, Layout.get super with
  | _, Const Any -> ok
  | Const c1, Const c2 when Layout.equal_const c1 c2 -> ok
  | Const Immediate, Const Immediate64 -> ok
  | Const (Immediate64 | Immediate), _ ->
    equality_check (Layout.equate super Layout.value)
  | _, _ -> equality_check (Layout.equate sub super)

