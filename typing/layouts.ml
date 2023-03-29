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

  type equate_result =
    | Unequal
    | Equal_mutated_first
    | Equal_mutated_second
    | Equal_no_mutation

  let swap_equate_result = function
    | Equal_mutated_first -> Equal_mutated_second
    | Equal_mutated_second -> Equal_mutated_first
    | (Unequal | Equal_no_mutation) as r -> r

  let equal_const_const c1 c2 = match c1, c2 with
    | Void, Void
    | Value, Value -> Equal_no_mutation
    | Void, Value
    | Value, Void -> Unequal

  let rec equate_var_const v1 c2 = match !v1 with
    | Some s1 -> equate_sort_const s1 c2
    | None -> v1 := Some (of_const c2); Equal_mutated_first

  and equate_var v1 s2 = match s2 with
    | Const c2 -> equate_var_const v1 c2
    | Var v2 -> equate_var_var v1 v2

  and equate_var_var v1 v2 =
    if v1 == v2 then
      Equal_no_mutation
    else begin
      match !v1, !v2 with
      | Some s1, _ -> swap_equate_result (equate_var v2 s1)
      | _, Some s2 -> equate_var v1 s2
      | None, None -> v1 := Some (of_var v2); Equal_mutated_first
    end

  and equate_sort_const s1 c2 = match s1 with
    | Const c1 -> equal_const_const c1 c2
    | Var v1 -> equate_var_const v1 c2

  let equate_tracking_mutation s1 s2 = match s1 with
    | Const c1 -> swap_equate_result (equate_sort_const s2 c1)
    | Var v1 -> equate_var v1 s2

  (* Don't expose whether or not mutation happened; we just need that for [Layout] *)
  let equate s1 s2 = match equate_tracking_mutation s1 s2 with
    | Unequal -> false
    | Equal_mutated_first | Equal_mutated_second | Equal_no_mutation -> true

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
  type fixed_layout_reason =
    | Let_binding
    | Function_argument
    | Function_result
    | Tuple_element
    | Probe
    | Package_hack
    | Object
    | Instance_variable
    | Object_field
    | Class_field

  type concrete_layout_reason =
    | Match
    | Constructor_declaration of int
    | Label_declaration of Ident.t

  type annotation_location =
    | Type_declaration of Path.t
    | Type_parameter of Path.t * string

  type reason =
    | Fixed_layout of fixed_layout_reason
    | Concrete_layout of concrete_layout_reason
    | Annotated of annotation_location
    | Gadt_equation of Path.t
    | Unified_with_tvar of string option
    | Dummy_reason_result_ignored

  type internal =
    | Any
    | Sort of sort
    | Immediate64
    (** We know for sure that values of types of this layout are always immediate
        on 64-bit platforms. For other platforms, we know nothing about immediacy.
    *)
    | Immediate

  type t =
    { layout : internal
    ; history : reason list (* events listed in reverse chronological order *)
    }
    (* XXX ASZ: Add this? *)
    (* ; creation : creation_reason *)

  let fresh_layout layout = { layout; history = [] }

  let add_reason reason t = { t with history = reason :: t.history }

  (******************************)
  (* constants *)

  let any = fresh_layout Any
  let void = fresh_layout (Sort Sort.void)
  let value = fresh_layout (Sort Sort.value)
  let immediate64 = fresh_layout Immediate64
  let immediate = fresh_layout Immediate

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

  let of_new_sort_var () = fresh_layout (Sort (Sort.new_var ()))

  let of_sort s = fresh_layout (Sort s)

  let of_const : const -> t = function
    | Any -> any
    | Immediate -> immediate
    | Immediate64 -> immediate64
    | Value -> value
    | Void -> void

  let of_const_option annot ~default =
    match annot with
    | None -> default
    | Some annot -> of_const annot

  let of_attributes ~reason ~default attrs =
    add_reason (Annotated reason) @@
    of_const_option ~default (Builtin_attributes.layout attrs)

  (******************************)
  (* elimination *)

  type desc =
    | Const of const
    | Var of Sort.var

  let repr ~default (t : t) : desc = match t.layout with
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

  module Formatting : sig
    open Format
    val format : formatter -> t -> unit
    val format_history :
      pp_name:(formatter -> 'a -> unit) -> name:'a ->
      formatter -> t -> unit
  end = struct
    open Format

    let format ppf t = fprintf ppf "%s" (to_string t)

    let fixed_layout_reason_layout = function
      | Let_binding
      | Function_argument
      | Function_result
      | Tuple_element
      | Probe
      | Package_hack
      | Object
      | Instance_variable
      | Object_field
      | Class_field
        -> value

    let format_fixed_layout_reason ppf =
      function
      | Let_binding -> fprintf ppf "let-bound"
      | Function_argument -> fprintf ppf "a function argument"
      | Function_result -> fprintf ppf "a function result"
      | Tuple_element -> fprintf ppf "a tuple element"
      | Probe -> fprintf ppf "a probe"
      | Package_hack -> fprintf ppf "involved in the package hack"
      (* CR layouts: figure out what "package hack" means *)
      | Object -> fprintf ppf "an object"
      | Instance_variable -> fprintf ppf "an instance variable"
      | Object_field -> fprintf ppf "an object field"
      | Class_field -> fprintf ppf "an class field"

    let format_concrete_layout_reason ppf : concrete_layout_reason -> unit =
      function
      | Match ->
        fprintf ppf "matched on"
      | Constructor_declaration idx ->
        fprintf ppf "used as constructor field %d" idx
      | Label_declaration lbl ->
        fprintf ppf "used in the declaration of the record field \"%a\""
          Ident.print lbl

    let format_annotation_location ppf : annotation_location -> unit = function
      | Type_declaration p ->
          fprintf ppf "the declaration of the type %a"
            Path.print p
      | Type_parameter (p, var) ->
          fprintf ppf "%s@ in the declaration of the type %a"
            var
            Path.print p

    let format_reason ppf : reason -> unit = function
      | Fixed_layout flr ->
          fprintf ppf "to@ %a because it was@ %a"
            format (fixed_layout_reason_layout flr)
            format_fixed_layout_reason flr
      | Concrete_layout clr ->
          fprintf ppf "to be concrete@ because it was %a"
            format_concrete_layout_reason clr
      | Annotated aloc ->
          fprintf ppf "by the annotation@ on %a"
            format_annotation_location aloc
      | Gadt_equation p ->
          fprintf ppf "by a GADT match@ on the constructor %a"
            Path.print p
      | Unified_with_tvar tv -> begin
          fprintf ppf "during unification@ with ";
          match tv with
          | None -> fprintf ppf "a type variable"
          | Some tv -> fprintf ppf "'%s" tv
        end
      | Dummy_reason_result_ignored ->
          Misc.fatal_errorf
            "Found [Dummy_reason_result_ignored] in a [layout] when printing!"

    let format_history ~pp_name ~name ppf t =
      (* XXX ASZ: Restore printing *)
      if false then begin
      let message ppf = function
        | 0 -> fprintf ppf "%a's layout was constrained" pp_name name
        | _ -> fprintf ppf "and"
      in
      List.iteri
        (fun i r ->
           fprintf ppf "@,@[<hov 2>%a %a@]"
             message i
             format_reason r)
        t.history
      end
  end

  include Formatting

  (******************************)
  (* errors *)

  module Violation = struct
    open Format

    type nonrec t =
      | Not_a_sublayout of t * t
      | No_intersection of t * t

    let report_general preamble pp_former former ppf t =
      let l1, problem, l2 = match t with
        | Not_a_sublayout(l1, l2) -> l1, "is not a sublayout of", l2
        | No_intersection(l1, l2) -> l1, "does not overlap with", l2
      in
      fprintf ppf "@[<v>@[<hov 2>%s%a has layout %a,@ which %s %a.@]%a%a@]"
        preamble
        pp_former former
        format l1
        problem
        format l2
        (format_history ~pp_name:pp_former ~name:former) l1
        (format_history ~pp_name:pp_print_string ~name:"The latter") l2

    let pp_t ppf x = fprintf ppf "%t" x

    let report_with_offender ~offender =
      report_general "" pp_t offender

    let report_with_offender_sort ~offender =
      report_general "A representable layout was expected, but " pp_t offender

    let report_with_name ~name =
      report_general "" pp_print_string name
end

  (******************************)
  (* relations *)

  let equate_or_equal ~allow_mutation (l1 : t) (l2 : t) =
    match l1.layout, l2.layout with
    | Any, Any -> true
    | Immediate64, Immediate64 -> true
    | Immediate, Immediate -> true
    | Sort s1, Sort s2 -> begin
        match Sort.equate_tracking_mutation s1 s2 with
        | (Equal_mutated_first | Equal_mutated_second)
          when not allow_mutation ->
            Misc.fatal_errorf
              "Layouts.Layout.equal: Performed unexpected mutation"
        | Unequal -> false
        | Equal_no_mutation | Equal_mutated_first | Equal_mutated_second -> true
      end
    | (Any | Immediate64 | Immediate | Sort _), _ -> false

  (* XXX ASZ: Switch this back to ~allow_mutation:false *)
  let equal = equate_or_equal ~allow_mutation:true

  let equate = equate_or_equal ~allow_mutation:true

  let intersection ~reason l1 l2 =
    let err = Error (Violation.No_intersection (l1, l2)) in
    let equality_check is_eq l = if is_eq then Ok l else err in
    (* it's OK not to cache the result of [get], because [get] does path
       compression *)
    Result.map (add_reason reason) @@ match get l1, get l2 with
    | Const Any, _ -> Ok { layout = l2.layout; history = l1.history }
    | _, Const Any -> Ok l1
    | Const c1, Const c2 when equal_const c1 c2 -> Ok l1
    | Const (Immediate64 | Immediate), Const (Immediate64 | Immediate) ->
         Ok immediate
    | Const ((Immediate64 | Immediate) as imm), l
    | l, Const ((Immediate64 | Immediate) as imm) ->
        equality_check (equate (of_desc l) value)
          (of_const imm)
    | _, _ -> equality_check (equate l1 l2) l1

  let sub ~reason sub super =
    let ok = Ok sub in
    let err = Error (Violation.Not_a_sublayout (sub,super)) in
    let equality_check is_eq = if is_eq then ok else err in
    Result.map (add_reason reason) @@ match get sub, get super with
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

    let internal ppf : internal -> unit = function
      | Any         -> fprintf ppf "Any"
      | Sort s      -> fprintf ppf "Sort %a" Sort.Debug_printers.t s
      | Immediate64 -> fprintf ppf "Immediate64"
      | Immediate   -> fprintf ppf "Immediate"

    let fixed_layout_reason ppf : fixed_layout_reason -> unit = function
      | Let_binding -> fprintf ppf "Let_binding"
      | Function_argument -> fprintf ppf "Function_argument"
      | Function_result -> fprintf ppf "Function_result"
      | Tuple_element -> fprintf ppf "Tuple_element"
      | Probe -> fprintf ppf "Probe"
      | Package_hack -> fprintf ppf "Package_hack"
      | Object -> fprintf ppf "Object"
      | Instance_variable -> fprintf ppf "Instance_variable"
      | Object_field -> fprintf ppf "Object_field"
      | Class_field -> fprintf ppf "Class_field"

    let concrete_layout_reason ppf : concrete_layout_reason -> unit = function
      | Match ->
          fprintf ppf "Match"
      | Constructor_declaration idx ->
          fprintf ppf "Constructor_declaration %d" idx
      | Label_declaration lbl ->
          fprintf ppf "Label_declaration %a" Ident.print lbl

    let annotation_location ppf : annotation_location -> unit = function
      | Type_declaration p ->
          fprintf ppf "Type_declaration %a" Path.print p
      | Type_parameter (p, var) ->
          fprintf ppf "(Type_parameter (%a, %S))" Path.print p var

    let reason ppf : reason -> unit = function
      | Fixed_layout flr ->
          fprintf ppf "Fixed_layout %a" fixed_layout_reason flr
      | Concrete_layout clr ->
          fprintf ppf "Concrete_layout %a" concrete_layout_reason clr
      | Annotated aloc ->
          fprintf ppf "Annotated %a" annotation_location aloc
      | Gadt_equation p ->
          fprintf ppf "Gadt_equation %a" Path.print p
      | Unified_with_tvar tv ->
          fprintf ppf "Unified_with_tvar %a"
            (Misc.Stdlib.Option.print pp_print_string) tv
      | Dummy_reason_result_ignored ->
          fprintf ppf "Dummy_reason_result_ignored"

    let reasons ppf (rs : reason list) : unit =
      fprintf ppf "@[<hov 2>[ %a@]@,]"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,; ") reason) rs

    let t ppf ({ layout; history } : t) : unit =
      fprintf ppf "@[<v 2>{ layout = %a@,; history = %a }@]"
        internal layout
        reasons  history
  end
end

type layout = Layout.t
