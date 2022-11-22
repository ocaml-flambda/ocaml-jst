(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                Chris Casinghino, Jane Street, New York                 *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Layouts *)

module Sort = struct
  type const =
    | Void
    | Value

  type t =
    | Var of var
    | Const of const
  and var = t option ref

  let void = Const Void
  let value = Const Value

  let of_const = function
    | Void -> void
    | Value -> value

  let of_var v = Var v

  let new_var () = Var (ref None)

  let rec repr ~default : t -> t = function
    | Const _ as t -> t
    | Var r as t -> begin match !r with
      | None -> begin match default with
        | None -> t
        | Some const -> begin
            let t = of_const const in
            r := Some t;
            t
          end
      end
      | Some s -> begin
          let result = repr ~default s in
          r := Some result; (* path compression *)
          result
        end
    end

  (***********************)
  (* equality *)

  let equal_const_const c1 c2 = match c1, c2 with
    | Void, Void -> true
    | Void, Value -> false
    | Value, Void -> false
    | Value, Value -> true

  let rec equate_var_const v1 c2 = match !v1 with
    | Some s1 -> equate_sort_const s1 c2
    | None -> v1 := Some (of_const c2); true

  and equate_var v1 s2 = match s2 with
    | Const c2 -> equate_var_const v1 c2
    | Var v2 -> equate_var_var v1 v2

  and equate_var_var v1 v2 = v1 == v2 || begin
    match !v1, !v2 with
    | Some s1, _ -> equate_var v2 s1
    | _, Some s2 -> equate_var v1 s2
    | None, None -> v1 := Some (of_var v2); true
  end

  and equate_sort_const s1 c2 = match s1 with
    | Const c1 -> equal_const_const c1 c2
    | Var v1 -> equate_var_const v1 c2

  and equate s1 s2 = match s1 with
    | Const c1 -> equate_sort_const s2 c1
    | Var v1 -> equate_var v1 s2

  module Debug_printers = struct
    open Format

    let rec t ppf = function
      | Var v   -> fprintf ppf "Var %a" var v
      | Const c -> fprintf ppf (match c with
                                | Void  -> "Void"
                                | Value -> "Value")

    and opt_t ppf = function
      | Some s -> fprintf ppf "Some %a" t s
      | None   -> fprintf ppf "None"

    and var ppf v = fprintf ppf "{ contents = %a }" opt_t (!v)
  end
end

type sort = Sort.t

module Layout = struct
  type t =
    | Any
    | Sort of sort
    | Immediate64
    (** We know for sure that values of types of this layout are always immediate
        on 64-bit platforms. For other platforms, we know nothing about immediacy.
    *)
    | Immediate

  (******************************)
  (* constants *)

  let any = Any
  let void = Sort Sort.void
  let value = Sort Sort.value
  let immediate64 = Immediate64
  let immediate = Immediate

  type const = Asttypes.const_layout =
    | Any
    | Value
    | Void
    | Immediate64
    | Immediate

  let string_of_const : const -> _ = function
    | Any -> "any"
    | Value -> "value"
    | Void -> "void"
    | Immediate64 -> "immediate64"
    | Immediate -> "immediate"

  let equal_const (c1 : const) (c2 : const) = match c1, c2 with
    | Any, Any -> true
    | Immediate64, Immediate64 -> true
    | Immediate, Immediate -> true
    | Void, Void -> true
    | Value, Value -> true
    | (Any | Immediate64 | Immediate | Void | Value), _ -> false

  (******************************)
  (* construction *)

  let of_new_sort_var () = Sort (Sort.new_var ())

  let of_sort s = Sort s

  let of_const : const -> t = function
    | Any -> Any
    | Immediate -> Immediate
    | Immediate64 -> Immediate64
    | Value -> value
    | Void -> void

  let of_const_option annot ~default =
    match annot with
    | None -> default
    | Some annot -> of_const annot

  let of_attributes ~default attrs =
    of_const_option ~default (Builtin_attributes.layout attrs)

  (******************************)
  (* elimination *)

  type desc =
    | Const of const
    | Var of Sort.var

  let repr ~default : t -> desc = function
    | Any -> Const Any
    | Immediate -> Const Immediate
    | Immediate64 -> Const Immediate64
    | Sort s -> begin match Sort.repr ~default s with
      (* NB: this match isn't as silly as it looks: those are
         different constructors on the left than on the right *)
      | Const Void -> Const Void
      | Const Value -> Const Value
      | Var v -> Var v
    end

  let get = repr ~default:None

  let of_desc = function
    | Const c -> of_const c
    | Var v -> of_sort (Sort.of_var v)

  (* CR layouts: this function is suspect; it seems likely to reisenberg
     that refactoring could get rid of it *)
  let sort_of_layout l =
    match get l with
    | Const Void -> Sort.void
    | Const (Value | Immediate | Immediate64) -> Sort.value
    | Const Any -> Misc.fatal_error "Layout.sort_of_layout"
    | Var v -> Sort.of_var v

  (*********************************)
  (* pretty printing *)

  let to_string lay = match get lay with
    | Const c -> string_of_const c
    | Var _ -> "<sort variable>"

  let format ppf t = Format.fprintf ppf "%s" (to_string t)

  (******************************)
  (* errors *)

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

  (******************************)
  (* relations *)

  let equate (l1 : t) (l2 : t) = match l1, l2 with
    | Any, Any -> true
    | Immediate64, Immediate64 -> true
    | Immediate, Immediate -> true
    | Sort s1, Sort s2 -> Sort.equate s1 s2
    | (Any | Immediate64 | Immediate | Sort _), _ -> false

  let intersection l1 l2 =
    let err = Error (Violation.No_intersection (l1, l2)) in
    let equality_check is_eq l = if is_eq then Ok l else err in
    (* it's OK not to cache the result of [get], because [get] does path
       compression *)
    match get l1, get l2 with
    | Const Any, _ -> Ok l2
    | _, Const Any -> Ok l1
    | Const c1, Const c2 when equal_const c1 c2 -> Ok l1
    | Const (Immediate64 | Immediate), Const (Immediate64 | Immediate) ->
      Ok immediate
    | Const ((Immediate64 | Immediate) as imm), l
    | l, Const ((Immediate64 | Immediate) as imm) ->
      equality_check (equate (of_desc l) value)
        (of_const imm)
    | _, _ -> equality_check (equate l1 l2) l1

  let sub sub super =
    let ok = Ok sub in
    let err = Error (Violation.Not_a_sublayout (sub,super)) in
    let equality_check is_eq = if is_eq then ok else err in
    match get sub, get super with
    | _, Const Any -> ok
    | Const c1, Const c2 when equal_const c1 c2 -> ok
    | Const Immediate, Const Immediate64 -> ok
    | Const (Immediate64 | Immediate), _ ->
      equality_check (equate super value)
    | _, _ -> equality_check (equate sub super)

  (*********************************)
  (* defaulting *)

  let get_defaulting ~default t =
    match repr ~default:(Some default) t with
    | Const result -> result
    | Var _ -> assert false

  let constrain_default_void = get_defaulting ~default:Sort.Void
  let can_make_void l = Void = constrain_default_void l
  let default_to_value t =
    ignore (get_defaulting ~default:Value t)

  (*********************************)
  (* debugging *)

  module Debug_printers = struct
    open Format

    let t ppf : t -> unit = function
      | Any         -> fprintf ppf "Any"
      | Sort s      -> fprintf ppf "Sort %a" Sort.Debug_printers.t s
      | Immediate64 -> fprintf ppf "Immediate64"
      | Immediate   -> fprintf ppf "Immediate"
  end
end

type layout = Layout.t
