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

module Sort : sig
  (** A sort classifies how a type is represented at runtime. Every concrete
      layout has a sort, and knowing the sort is sufficient for knowing the
      calling convention of values of a given type. *)
  type t

  (** These are the constant sorts -- fully determined and without variables *)
  type const =
    | Void
      (** No run time representation at all *)
    | Value
      (** Standard ocaml value representation *)

  (** A sort variable that can be unified during type-checking. *)
  type var

  (** Create a new sort variable that can be unified. *)
  val new_var : unit -> t

  val of_const : const -> t
  val of_var : var -> t

  val void : t
  val value : t

  (** This checks for equality, and sets any variables to make two sorts
      equal, if possible *)
  val equate : t -> t -> bool

  module Debug_printers : sig
    val t : Format.formatter -> t -> unit
    val var : Format.formatter -> var -> unit
  end
end

type sort = Sort.t

(** This module describes layouts, which classify types. Layouts are arranged
    in the following lattice:

    {[
                any
              /    \
           value  void
             |
         immediate64
             |
         immediate
    ]}
*)
module Layout : sig
  (** A Layout.t is a full description of the runtime representation of values
      of a given type. It includes sorts, but also the abstract top layout
      [Any] and sublayouts of other sorts, such as [Immediate]. *)
  type t

  (******************************)
  (* constants *)

  (** Constant layouts are used both for user-written annotations and within
      the type checker when we know a layout has no variables *)
  type const = Asttypes.const_layout =
    | Any
    | Value
    | Void
    | Immediate64
    | Immediate
  val string_of_const : const -> string
  val equal_const : const -> const -> bool

  (** This layout is the top of the layout lattice. All types have layout [any].
      But we cannot compile run-time manipulations of values of types with layout
      [any].

      If [missing_cmi_for] is [None], this value is guaranteed to be shared. *)
  val any : missing_cmi_for:Path.t option -> t

  (** Value of types of this layout are not retained at all at runtime *)
  val void : t

  (** This is the layout of normal ocaml values *)
  val value : t

  (** Values of types of this layout are immediate on 64-bit platforms; on other
      platforms, we know nothing other than that it's a value. *)
  val immediate64 : t

  (** We know for sure that values of types of this layout are always immediate *)
  val immediate : t

  (******************************)
  (* errors *)

  (* XXX ASZ: Rename to "xxx_layout_context"? *)
  type fixed_layout_reason =
    | Let_binding
    | Function_argument
    | Function_result
    | Tuple_element
    | Probe
    | Package_hack
    | Object
    | Instance_variable
    | Object_field (* XXX ASZ: Is this different than [Instance_variable]? *)
    | Class_field

  type concrete_layout_reason =
    | Match
    | Constructor_declaration of int
    | Label_declaration of Ident.t

  type annotation_location =
    | Type_declaration of Path.t
    | Type_parameter of Path.t * string
    | With_constraint of Location.t
    | Newtype_declaration of string Location.loc

  type reason =
    | Fixed_layout of fixed_layout_reason
    | Concrete_layout of concrete_layout_reason
    | Annotated of annotation_location
    | Gadt_equation of Path.t
    | Unified_with_tvar of string option
        (* XXX ASZ: RAE thinks this will want to take a type, not a tvar name
           (string option) in case that type gets further unified.  He's
           probably right but we'll see how errors look. *)
    | V1_safety_check
    | Dummy_reason_result_ignored
        (* XXX ASZ: Is this the best approach?  Where could we insert a "last
           resort" check to indicate that we shouldn't be seeing this? *)

  module Violation : sig
    type nonrec t =
      | Not_a_sublayout of t * t
      | No_intersection of t * t

    (* CR layouts: Having these options for printing a violation was a choice
       made based on the needs of expedient debugging during development, but
       probably should be rethought at some point. *)
    (** Prints a violation and the thing that had an unexpected layout
        ([offender], which you supply an arbitrary printer for). *)
    val report_with_offender :
      offender:(Format.formatter -> unit) -> Format.formatter -> t -> unit

    (** Like [report_with_offender], but additionally prints that the issue is
        that a representable layout was expected. *)
    val report_with_offender_sort :
      offender:(Format.formatter -> unit) -> Format.formatter -> t -> unit

    (** Simpler version of [report_with_offender] for when the thing that had an
        unexpected layout is available as a string. *)
    val report_with_name : name:string -> Format.formatter -> t -> unit
  end

  (******************************)
  (* construction *)

  (** Create a fresh sort variable, packed into a layout. *)
  val of_new_sort_var : unit -> t

  val of_sort : sort -> t
  val of_const : const -> t

  (** Find a layout in attributes.  Returns error if a disallowed layout is
      present, but always allows immediate attributes if ~legacy_immediate is
      true.  See comment on [Builtin_attributes.layout].  *)
  val of_attributes :
    legacy_immediate:bool -> reason:annotation_location -> Parsetree.attributes ->
    (t option, Location.t * const) result

  (** Find a layout in attributes, defaulting to ~default.  Returns error if a
      disallowed layout is present, but always allows immediate if
      ~legacy_immediate is true.  See comment on [Builtin_attributes.layout]. *)
  val of_attributes_default :
    legacy_immediate:bool -> reason:annotation_location ->
    default:t -> Parsetree.attributes ->
    (t, Location.t * const) result

  (******************************)
  (* elimination *)

  type desc =
    | Const of const
    | Var of Sort.var

  (** Extract the [const] from a [Layout.t], looking through unified
      sort variables. Returns [Var] if the final, non-variable layout has not
      yet been determined. *)
  val get : t -> desc

  val of_desc : desc -> t

  (** Returns the sort corresponding to the layout.  Call only on representable
      layouts - raises on Any. *)
  val sort_of_layout : t -> sort

  (*********************************)
  (* pretty printing *)

  val to_string : t -> string
  val format : Format.formatter -> t -> unit
  val format_history :
    pp_name:(Format.formatter -> 'a -> unit) -> name:'a ->
    Format.formatter -> t -> unit

  (******************************)
  (* relations *)

  (** This checks for equality, and sets any variables to make two layouts
      equal, if possible. e.g. [equate] on a var and [value] will set the
      variable to be [value].

      This function ignores the [missing_cmi_for] medatadata for [any]s. *)
  val equate : t -> t -> bool

  (** This checks for equality, but has the invariant that it can only be called
      when there is no need for unification; e.g. [equal] on a var and [value]
      will crash.

      This function ignores the [missing_cmi_for] medatadata for [any]s.

      XXX ASZ: At the moment, this is actually the same as [equate]! *)
  val equal : t -> t -> bool

  (** Finds the intersection of two layouts, constraining sort variables to
      create one if needed, or returns a [Violation.t] if an intersection does
      not exist.  Can update the layouts.  The returned layout's history
      consists of the provided reason followed by the history of the first
      layout argument.  That is, due to histories, this function is asymmetric;
      it should be thought of as modifying the first layout to be the
      intersection of the two, not something that modifies the second layout. *)
  val intersection : reason:reason -> t -> t -> (t, Violation.t) Result.t

  (** [sub t1 t2] returns [Ok t1] iff [t1] is a sublayout of
    of [t2].  The current hierarchy is:

    Any > Sort Value > Immediate64 > Immediate
    Any > Sort Void

    Returns [Error _] if the coercion is not possible. *)
  val sub : t -> t -> (unit, Violation.t) result

  (*********************************)
  (* defaulting *)
  val constrain_default_void : t -> const
  val can_make_void : t -> bool
  (* XXX layouts: make sure uses of these functions have been changed to default
     to value before releasing. *)

  val default_to_value : t -> unit

  (*********************************)
  (* debugging *)

  module Debug_printers : sig
    val t : Format.formatter -> t -> unit
  end
end

type layout = Layout.t
