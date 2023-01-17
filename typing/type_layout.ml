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

  let rec constrain_sort_default_void = function
    | Types.Void -> Asttypes.Void
    | Types.Value -> Asttypes.Value
    | Types.Var r ->
      match !r with
      | Some sort -> constrain_sort_default_void sort
      | None -> (r := Some Types.Void; Asttypes.Void)

  let constrain_default_void = function
    | Types.Any -> Asttypes.Any
    | Types.Sort sort -> constrain_sort_default_void sort
    | Types.Immediate64 -> Asttypes.Immediate64
    | Types.Immediate -> Asttypes.Immediate

  let can_make_void l = Asttypes.Void = constrain_default_void l
end

let of_const_layout = function
  | Asttypes.Any         -> Any
  | Asttypes.Value       -> Sort Value
  | Asttypes.Void        -> Sort Void
  | Asttypes.Immediate64 -> Immediate64
  | Asttypes.Immediate   -> Immediate

let of_const_layout_opt annot_opt ~default =
  match annot_opt with
  | None -> default
  | Some {Location.txt = annot} -> of_const_layout annot

let of_attributes ~default attrs =
  of_const_layout_opt ~default (Builtin_attributes.layout attrs)

let rec sort_to_string = function
  | Var r -> begin
    match !r with
    | Some s -> sort_to_string s
    | None -> "<sort variable>"
  end
  | Value -> "value"
  | Void -> "void"

let to_string = function
  | Any -> "any"
  | Sort sort -> sort_to_string sort
  | Immediate64 -> "immediate64"
  | Immediate -> "immediate"

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

let sort_var () = Var (ref None)

let any = Any
let any_sort () = Sort (sort_var ())
let value = Sort Value
let immediate = Immediate
let immediate64 = Immediate64
let void = Sort Void

let rec sort_repr s =
  match s with
  | (Value | Void) -> s
  | Var r -> begin
      match !r with
      | Some s -> sort_repr s
      | None -> s
    end

let repr l =
  match l with
  | (Any | Immediate | Immediate64) -> l
  | Sort s -> Sort (sort_repr s)

let all_void layouts =
  Array.for_all (fun l ->
    match repr l with
    | Sort Void -> true
    | (Any | Immediate | Immediate64
      | Sort (Value | Var _)) -> false) layouts

let sort_of_layout l =
  match repr l with
  | Sort s -> s
  | Immediate | Immediate64 -> Value
  | Any -> Misc.fatal_error "Type_layout.sort_of_layout"

let layout_bound_of_record_representation = function
  | Record_unboxed l -> l
  | Record_float -> value
  | Record_inlined (tag,rep) -> begin
      match (tag,rep) with
      | Extension _, _ -> value
      | _, Variant_extensible -> value
      | Ordinary _, Variant_unboxed l -> l (* n must be 0 here *)
      | Ordinary {src_index}, Variant_boxed layouts ->
        if all_void layouts.(src_index) then immediate else value
    end
  | Record_boxed layouts when all_void layouts -> immediate
  | Record_boxed _ -> value

let cstr_layouts_immediate layouts = Array.for_all all_void layouts

let layout_bound_of_variant_representation = function
    Variant_unboxed l -> l
  | Variant_boxed layouts ->
    if cstr_layouts_immediate layouts then immediate else value
  | Variant_extensible -> value

(* should not mutate sorts *)
let layout_bound_of_kind = function
  | Type_abstract { layout } -> layout
  | Type_open -> value
  | Type_record (_,rep) -> layout_bound_of_record_representation rep
  | Type_variant (_, rep) -> layout_bound_of_variant_representation rep

let default_to_value t =
  match repr t with
  | (Any | Immediate | Immediate64
     | Sort (Value | Void | Var { contents = Some _ })) -> ()
  | Sort (Var ({contents = None} as r)) -> r := Some Value

let equal_sort s1 s2 =
  match sort_repr s1, sort_repr s2 with
  | Value, Value -> true
  | Void, Void -> true
  | (Var r, Var s) when s == r -> true
  (* The use of [sort_repr] and this physical equality check amount to an
     "occurs" check that prevents creating a circular reference in the
     assignment case. *)
  | (Var r, s) | (s, Var r) -> (r := Some s; true)
  | (Value | Void), _ -> false

let equal l1 l2 =
  match l1, l2 with
  | Any, Any
  | Immediate64, Immediate64
  | Immediate, Immediate -> true
  | Sort s1, Sort s2 -> equal_sort s1 s2
  | (Any | Immediate64 | Immediate | Sort _), _ -> false

let intersection l1 l2 =
  match l1, l2 with
  | (Any, l | l, Any) -> Ok l
  | ( (Immediate64 | Immediate) as l, Sort s
    | Sort s, ((Immediate64 | Immediate) as l)) ->
    if equal_sort Value s then Ok l
    else Error (Violation.No_intersection (l1, l2))
  | (Immediate, Immediate64 | Immediate64, Immediate) -> Ok Immediate64
  | _, _ ->
    if equal l1 l2 then Ok l2 else Error (Violation.No_intersection (l1, l2))

let sublayout sub super =
  match sub, super with
  | _, Any -> Ok sub
  | (Immediate64 | Immediate), Sort s ->
      if equal_sort Value s then Ok sub
      else Error (Violation.Not_a_sublayout (sub,super))
  | Immediate, Immediate64 -> Ok sub
  | _, _ ->
      if equal sub super then Ok sub
      else Error (Violation.Not_a_sublayout (sub,super))

(** This is used in reify.  We default to value as a hack to avoid having rigid
    sort variables. *)
let reify_sort s =
  match sort_repr s with
  | Var r -> begin
      match !r with
      | None -> r := Some Value
      | Some _ -> ()
    end
  | _ -> ()

let reify layout =
  match layout with
  | Sort s -> reify_sort s
  | (Any | Immediate64 | Immediate) -> ()
