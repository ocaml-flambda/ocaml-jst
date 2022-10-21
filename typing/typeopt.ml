(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1998 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Auxiliaries for type-based optimizations, e.g. array kinds *)

open Path
open Types
open Asttypes
open Typedtree
open Lambda

let scrape_ty env ty =
  let ty = Ctype.expand_head_opt env (Ctype.correct_levels ty) in
  match ty.desc with
  | Tconstr (p, _, _) ->
      begin match Env.find_type p env with
      | {type_kind = ( Type_variant (_, Variant_unboxed _)
                     | Type_record (_, Record_unboxed (_,_)) ); _} ->
        Ctype.get_unboxed_type_representation env ty
      | _ -> ty
      | exception Not_found -> ty
      end
  | _ -> ty

let scrape env ty =
  (scrape_ty env ty).desc

let is_function_type env ty =
  match scrape env ty with
  | Tarrow (_, lhs, rhs, _) -> Some (lhs, rhs)
  | _ -> None

let is_base_type env ty base_ty_path =
  match scrape env ty with
  | Tconstr(p, _, _) -> Path.same p base_ty_path
  | _ -> false

let maybe_pointer_type env ty =
  if Ctype.maybe_pointer_type env ty then
    Pointer
  else
    Immediate

let maybe_pointer exp = maybe_pointer_type exp.exp_env exp.exp_type

let is_void_type env ty = Ctype.is_void_type env (Ctype.correct_levels ty)

let is_void exp = is_void_type exp.exp_env exp.exp_type

type classification =
  | Int
  | Float
  | Lazy
  | Addr  (* anything except a float or a lazy *)
  | Any

let classify env ty =
  let ty = scrape_ty env ty in
  if maybe_pointer_type env ty = Immediate then Int
  else match ty.desc with
  | Tvar _ | Tunivar _ ->
      Any
  | Tconstr (p, _args, _abbrev) ->
      if Path.same p Predef.path_float then Float
      else if Path.same p Predef.path_lazy_t then Lazy
      else if Path.same p Predef.path_string
           || Path.same p Predef.path_bytes
           || Path.same p Predef.path_array
           || Path.same p Predef.path_nativeint
           || Path.same p Predef.path_int32
           || Path.same p Predef.path_int64 then Addr
      else begin
        try
          match (Env.find_type p env).type_kind with
          | Type_abstract _ ->
              Any
          | Type_record _ | Type_variant _ | Type_open ->
              Addr
        with Not_found ->
          (* This can happen due to e.g. missing -I options,
             causing some .cmi files to be unavailable.
             Maybe we should emit a warning. *)
          Any
      end
  | Tarrow _ | Ttuple _ | Tpackage _ | Tobject _ | Tnil | Tvariant _ ->
      Addr
  | Tlink _ | Tsubst _ | Tpoly _ | Tfield _ ->
      assert false

let array_type_kind env ty =
  match scrape env ty with
  | Tconstr(p, [elt_ty], _) | Tpoly({desc = Tconstr(p, [elt_ty], _)}, _)
    when Path.same p Predef.path_array ->
      begin match classify env elt_ty with
      | Any -> if Config.flat_float_array then Pgenarray else Paddrarray
      | Float -> if Config.flat_float_array then Pfloatarray else Paddrarray
      | Addr | Lazy -> Paddrarray
      | Int -> Pintarray
      end
  | Tconstr(p, [], _) | Tpoly({desc = Tconstr(p, [], _)}, _)
    when Path.same p Predef.path_floatarray ->
      Pfloatarray
  | _ ->
      (* This can happen with e.g. Obj.field *)
      Pgenarray

let array_kind exp = array_type_kind exp.exp_env exp.exp_type

let array_pattern_kind pat = array_type_kind pat.pat_env pat.pat_type

let bigarray_decode_type env ty tbl dfl =
  match scrape env ty with
  | Tconstr(Pdot(Pident mod_id, type_name), [], _)
    when Ident.name mod_id = "Stdlib__Bigarray" ->
      begin try List.assoc type_name tbl with Not_found -> dfl end
  | _ ->
      dfl

let kind_table =
  ["float32_elt", Pbigarray_float32;
   "float64_elt", Pbigarray_float64;
   "int8_signed_elt", Pbigarray_sint8;
   "int8_unsigned_elt", Pbigarray_uint8;
   "int16_signed_elt", Pbigarray_sint16;
   "int16_unsigned_elt", Pbigarray_uint16;
   "int32_elt", Pbigarray_int32;
   "int64_elt", Pbigarray_int64;
   "int_elt", Pbigarray_caml_int;
   "nativeint_elt", Pbigarray_native_int;
   "complex32_elt", Pbigarray_complex32;
   "complex64_elt", Pbigarray_complex64]

let layout_table =
  ["c_layout", Pbigarray_c_layout;
   "fortran_layout", Pbigarray_fortran_layout]

let bigarray_type_kind_and_layout env typ =
  match scrape env typ with
  | Tconstr(_p, [_caml_type; elt_type; layout_type], _abbrev) ->
      (bigarray_decode_type env elt_type kind_table Pbigarray_unknown,
       bigarray_decode_type env layout_type layout_table
                            Pbigarray_unknown_layout)
  | _ ->
      (Pbigarray_unknown, Pbigarray_unknown_layout)

let value_kind env ty =
  let rec loop env ~visited ~depth ~num_nodes_visited ty
      : int * layout_rep =
    let[@inline] cannot_proceed () =
      Numbers.Int.Set.mem ty.id visited
        || depth >= 2
        || num_nodes_visited >= 30
    in
    match scrape env ty with
    | Tconstr(p, _, _) when Path.same p Predef.path_int ->
      (num_nodes_visited, Value Pintval)
    | Tconstr(p, _, _) when Path.same p Predef.path_char ->
      (num_nodes_visited, Value Pintval)
    | Tconstr(p, _, _) when Path.same p Predef.path_float ->
      (num_nodes_visited, Value Pfloatval)
    | Tconstr(p, _, _) when Path.same p Predef.path_int32 ->
      (num_nodes_visited, Value (Pboxedintval Pint32))
    | Tconstr(p, _, _) when Path.same p Predef.path_int64 ->
      (num_nodes_visited, Value (Pboxedintval Pint64))
    | Tconstr(p, _, _) when Path.same p Predef.path_nativeint ->
      (num_nodes_visited, Value (Pboxedintval Pnativeint))
    | Tconstr(p, _, _)
        when (Path.same p Predef.path_array
              || Path.same p Predef.path_floatarray) ->
     (num_nodes_visited, Value (Parrayval (array_type_kind env ty)))
    | Tconstr(p, _, _) ->
      if cannot_proceed () then
        (num_nodes_visited, Value Pgenval)
      else begin
        let visited = Numbers.Int.Set.add ty.id visited in
        match (Env.find_type p env).type_kind with
        | exception Not_found ->
          (num_nodes_visited, Value Pgenval)
        (* CJC XXX in what cases do we hit this Not_found?  Missing cmis?  Is it
           safe to assume Pgenval here still?

           No, it isn't.  We need to rework the whole lambda translation so that
           this is only called on values.  We can achieve that by storing
           layouts in the typed tree at places where the layout isn't clear from
           the context.  *)
        | Type_variant (constructors, rep) -> begin
          match rep with
          | Variant_immediate -> (num_nodes_visited, Value Pintval)
          | (Variant_regular | Variant_unboxed _) ->
            let depth = depth + 1 in
            let for_one_constructor
                  (constructor : Types.constructor_declaration)
                  ~depth ~num_nodes_visited =
              let num_nodes_visited = num_nodes_visited + 1 in
              match constructor.cd_args with
              (* CJC XXX transform these case to pull the num_nodes_visited out of the match *)
              | Cstr_tuple fields ->
                let num_nodes_visited, kinds =
                  List.fold_left
                    (fun (num_nodes_visited, kinds) field ->
                       let num_nodes_visited = num_nodes_visited + 1 in
                       match loop env ~visited ~depth ~num_nodes_visited field
                       with
                       | (num_nodes_visited, Void) ->
                         (num_nodes_visited, kinds)
                       | (num_nodes_visited, Value kind) ->
                         (num_nodes_visited, kind :: kinds))
                    (num_nodes_visited, []) fields
                in
                (false, num_nodes_visited), List.rev kinds
              | Cstr_record labels ->
                let is_mutable, num_nodes_visited, kinds =
                  List.fold_left
                    (fun (is_mutable, num_nodes_visited, kinds)
                         (label:Types.label_declaration) ->
                        let num_nodes_visited = num_nodes_visited + 1 in
                        let num_nodes_visited, kinds, field_mutable =
                          match loop env ~visited ~depth ~num_nodes_visited
                                  label.ld_type with
                          | (num_nodes_visited, Void) ->
                            (num_nodes_visited, kinds, Asttypes.Immutable)
                          | (num_nodes_visited, Value kind) ->
                            (num_nodes_visited, kind :: kinds, label.ld_mutable)
                        in
                        let is_mutable =
                          match field_mutable with
                          | Mutable -> true
                          | Immutable -> is_mutable
                        in
                        is_mutable, num_nodes_visited, kinds)
                    (false, num_nodes_visited, []) labels
                in
                (is_mutable, num_nodes_visited), List.rev kinds
            in
            let result =
              List.fold_left (fun result constructor ->
                  match result with
                  | None -> None
                  | Some (num_nodes_visited,
                          next_const, consts, next_tag, non_consts) ->
                    let (is_mutable, num_nodes_visited), fields =
                      for_one_constructor constructor ~depth ~num_nodes_visited
                    in
                    if is_mutable then None
                    else if List.compare_length_with fields 0 = 0 then
                      let consts = next_const :: consts in
                      Some (num_nodes_visited,
                        next_const + 1, consts, next_tag, non_consts)
                    else
                      let non_consts = (next_tag, fields) :: non_consts in
                      Some (num_nodes_visited,
                        next_const, consts, next_tag + 1, non_consts))
                (Some (num_nodes_visited, 0, [], 0, []))
                constructors
            in
            begin match result with
            | None -> (num_nodes_visited, Value Pgenval)
            | Some (num_nodes_visited, _, consts, _, non_consts) ->
              match non_consts with
              | [] -> assert false
                (* Should be handled by the Variant_immediate case above *)
              | _::_ ->
                (num_nodes_visited, Value (Pvariant { consts; non_consts }))
            end
          end
        | Type_record (labels, record_representation) ->
          let depth = depth + 1 in
          let is_mutable, num_nodes_visited, kinds =
            List.fold_left
             (fun (is_mutable, num_nodes_visited, kinds)
                  (label:Types.label_declaration) ->
                 let num_nodes_visited = num_nodes_visited + 1 in
                 let num_nodes_visited, kinds, field_mutable =
                   match loop env ~visited ~depth ~num_nodes_visited
                           label.ld_type with
                   | (num_nodes_visited, Void) ->
                     (num_nodes_visited, kinds, Asttypes.Immutable)
                   | (num_nodes_visited, Value kind) ->
                     (num_nodes_visited, kind :: kinds, label.ld_mutable)
                 in
                 let is_mutable =
                   match field_mutable with
                   | Mutable -> true
                   | Immutable -> is_mutable
                 in
                 is_mutable, num_nodes_visited, kinds)
             (false, num_nodes_visited, []) labels
          in
          let kinds = List.rev kinds in
          if is_mutable then
            num_nodes_visited, Value Pgenval
          else begin match record_representation with
            | Record_regular ->
              (num_nodes_visited,
               Value (Pvariant { consts = []; non_consts = [0, kinds] }))
            | Record_float ->
              (num_nodes_visited,
               Value (Pvariant {
                 consts = [];
                 non_consts = [
                   Obj.double_array_tag,
                   List.map (fun _ -> Pfloatval) kinds
                 ] }))
            | Record_inlined tag ->
              (num_nodes_visited,
               Value (Pvariant { consts = []; non_consts = [tag, kinds] }))
            | Record_unboxed _ ->
              begin match kinds with
              | [kind] -> (num_nodes_visited, Value kind)
              | [] -> (num_nodes_visited, Void)
              | _::_ ->
                Misc.fatal_error "Records that are [Record_unboxed] should \
                  have at most one runtime field"
              end
            | Record_extension _ ->
              (num_nodes_visited, Value Pgenval)
            | Record_immediate _ ->
              (num_nodes_visited, Value Pintval)
          end
        | Type_abstract {layout} ->
          let kind =
            match Type_layout.Constant.constrain_default_void layout with
            | Any -> Misc.fatal_error "Typeopt value_kind"
            | Value -> Value Pgenval
            | Immediate64 -> Value Pintval
            | Immediate -> Value Pintval
            | Void -> Void
          in
          num_nodes_visited, kind
        | Type_open -> num_nodes_visited, Value Pgenval
      end
    | Ttuple fields ->
      if cannot_proceed () then
        num_nodes_visited, Value Pgenval
      else begin
        let visited = Numbers.Int.Set.add ty.id visited in
        let depth = depth + 1 in
        let num_nodes_visited, fields =
          List.fold_left
            (fun (num_nodes_visited, kinds) field ->
               let num_nodes_visited = num_nodes_visited + 1 in
               match loop env ~visited ~depth ~num_nodes_visited field
               with
               | (num_nodes_visited, Void) ->
                 (num_nodes_visited, kinds)
               | (num_nodes_visited, Value kind) ->
                 (num_nodes_visited, kind :: kinds))
            (num_nodes_visited, []) fields
        in
        num_nodes_visited,
          Value (Pvariant { consts = []; non_consts = [0, List.rev fields] })
      end
    | _ ->
      num_nodes_visited, Value Pgenval
  in
  let (_num_nodes_visited, layout_rep) =
    loop env ~visited:Numbers.Int.Set.empty ~depth:0
      ~num_nodes_visited:0 ty
  in
  layout_rep

let function_return_value_kind env ty =
  match is_function_type env ty with
  | Some (_lhs, rhs) -> begin
      match value_kind env rhs with
      | Value k -> k
      | Void -> assert false
    end
  | None -> Pgenval

let value_kind_of_layout = function
  | Value kind -> kind
  | Void -> assert false

(** Whether a forward block is needed for a lazy thunk on a value, i.e.
    if the value can be represented as a float/forward/lazy *)
let lazy_val_requires_forward env ty =
  match classify env ty with
  | Any | Lazy -> true
  | Float -> Config.flat_float_array
  | Addr | Int -> false

(** The compilation of the expression [lazy e] depends on the form of e:
    constants, floats and identifiers are optimized.  The optimization must be
    taken into account when determining whether a recursive binding is safe. *)
let classify_lazy_argument : Typedtree.expression ->
                             [`Constant_or_function
                             |`Float_that_cannot_be_shortcut
                             |`Identifier of [`Forward_value|`Other]
                             |`Other] =
  fun e -> match e.exp_desc with
    | Texp_constant
        ( Const_int _ | Const_char _ | Const_string _
        | Const_int32 _ | Const_int64 _ | Const_nativeint _ )
    | Texp_function _
    | Texp_construct (_, {cstr_arity = 0}, _) ->
       `Constant_or_function
    | Texp_constant(Const_float _) ->
       if Config.flat_float_array
       then `Float_that_cannot_be_shortcut
       else `Constant_or_function
    | Texp_ident _ when lazy_val_requires_forward e.exp_env e.exp_type ->
       `Identifier `Forward_value
    | Texp_ident _ ->
       `Identifier `Other
    | _ ->
       `Other

let value_kind_union (k1 : Lambda.value_kind) (k2 : Lambda.value_kind) =
  if Lambda.equal_value_kind k1 k2 then k1
  else Pgenval
