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

(* Expand a type, looking through ordinary synonyms, private synonyms,
   links, and [@@unboxed] types. The returned type will be therefore be none
   of these cases. *)
let scrape_ty env ty =
  let ty =
    match get_desc ty with
    | Tpoly(ty, _) -> ty
    | _ -> ty
  in
  match get_desc ty with
  | Tconstr _ ->
      let ty = Ctype.expand_head_opt env (Ctype.correct_levels ty) in
      begin match get_desc ty with
      | Tconstr (p, _, _) ->
          begin match Env.find_type p env with
          | {type_kind = ( Type_variant (_, Variant_unboxed _)
                         | Type_record (_, Record_unboxed _) ); _} ->
            Ctype.get_unboxed_type_representation env ty
          | _ -> ty
          | exception Not_found -> ty
          end
      | _ ->
          ty
      end
  | _ -> ty

(* See [scrape_ty]; this returns the [type_desc] of a scraped [type_expr]. *)
let scrape env ty =
  get_desc (scrape_ty env ty)

let scrape_poly env ty =
  let ty = scrape_ty env ty in
  match get_desc ty with
  | Tpoly (ty, _) -> get_desc ty
  | d -> d

let is_function_type env ty =
  match scrape env ty with
  | Tarrow (_, lhs, rhs, _) -> Some (lhs, rhs)
  | _ -> None

let is_base_type env ty base_ty_path =
  match scrape env ty with
  | Tconstr(p, _, _) -> Path.same p base_ty_path
  | _ -> false

let maybe_pointer_type env ty =
  if Ctype.is_immediate env ty then Immediate else Pointer

let maybe_pointer exp = maybe_pointer_type exp.exp_env exp.exp_type

type classification =
  | Int   (* any immediate type *)
  | Float
  | Lazy
  | Addr  (* anything except a float or a lazy *)
  | Any

(* Classify a ty into a [classification]. Looks through synonyms, using [scrape_ty].
   Returning [Any] is safe, though may skip some optimizations. *)
let classify env ty : classification =
  let ty = scrape_ty env ty in
  if maybe_pointer_type env ty = Immediate then Int
  else match get_desc ty with
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
  match scrape_poly env ty with
  | Tconstr(p, [elt_ty], _) when Path.same p Predef.path_array ->
      begin match classify env elt_ty with
      | Any -> if Config.flat_float_array then Pgenarray else Paddrarray
      | Float -> if Config.flat_float_array then Pfloatarray else Paddrarray
      | Addr | Lazy -> Paddrarray
      | Int -> Pintarray
      end
  | Tconstr(p, [], _) when Path.same p Predef.path_floatarray ->
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

let value_kind_of_value_layout layout =
  match Type_layout.Const.constrain_default_void layout with
  | Value -> Pgenval
  | Immediate -> Pintval
  | Immediate64 ->
    if !Clflags.native_code && Sys.word_size = 64 then Pintval else Pgenval
  | Any | Void -> assert false

(* Invariant: [value_kind] functions may only be called on types with layout
   value. *)
let rec value_kind env ~visited ~depth ~num_nodes_visited ty
  : int * value_kind =
  let[@inline] cannot_proceed () =
    Numbers.Int.Set.mem (get_id ty) visited
    || depth >= 2
    || num_nodes_visited >= 30
  in
  (* CJC XXX remove this check once all of jane builds *)
  begin match Ctype.(check_type_layout env (correct_levels ty) Layout.void) with
  | Ok _ -> assert false
  | _ -> ()
  end;
  let scty = scrape_ty env ty in
  match get_desc scty with
  | Tconstr(p, _, _) when Path.same p Predef.path_int ->
    (num_nodes_visited, Pintval)
  | Tconstr(p, _, _) when Path.same p Predef.path_char ->
    (num_nodes_visited, Pintval)
  | Tconstr(p, _, _) when Path.same p Predef.path_float ->
    (num_nodes_visited, Pfloatval)
  | Tconstr(p, _, _) when Path.same p Predef.path_int32 ->
    (num_nodes_visited, (Pboxedintval Pint32))
  | Tconstr(p, _, _) when Path.same p Predef.path_int64 ->
    (num_nodes_visited, (Pboxedintval Pint64))
  | Tconstr(p, _, _) when Path.same p Predef.path_nativeint ->
    (num_nodes_visited, (Pboxedintval Pnativeint))
  | Tconstr(p, _, _)
    when (Path.same p Predef.path_array
          || Path.same p Predef.path_floatarray) ->
    (num_nodes_visited, Parrayval (array_type_kind env ty))
  | Tconstr(p, _, _) -> begin
    try
      let kind = (Env.find_type p env).type_kind in
      if cannot_proceed () then
        num_nodes_visited,
        value_kind_of_value_layout (Type_layout.layout_bound_of_kind kind)
      else
        let visited = Numbers.Int.Set.add (get_id ty) visited in
        match kind with
        | Type_variant (cstrs, rep) ->
          value_kind_variant env ~visited ~depth ~num_nodes_visited cstrs rep
        | Type_record (labels, rep) ->
          let depth = depth + 1 in
          value_kind_record env ~visited ~depth ~num_nodes_visited labels rep
        | Type_abstract {layout} ->
          num_nodes_visited,
          value_kind_of_value_layout layout
        | Type_open -> num_nodes_visited, Pgenval
    with Not_found -> num_nodes_visited, Pgenval
      (* Safe to assume Pgenval in Not_found case because of the invariant
         that [value_kind] is only called on types of layout value *)
    end
  | Ttuple fields ->
    if cannot_proceed () then
      num_nodes_visited, Pgenval
    else begin
      let visited = Numbers.Int.Set.add (get_id ty) visited in
      let depth = depth + 1 in
      let num_nodes_visited, fields =
        List.fold_left
          (fun (num_nodes_visited, kinds) field ->
             let num_nodes_visited = num_nodes_visited + 1 in
             (* CR ccasinghino - this is fine because voids are not allowed in
                tuples.  When they are, we probably need to add a list of
                layouts to Ttuple, as in variant_representation and
                record_representation *)
             let num_nodes_visited, kind =
               value_kind env ~visited ~depth ~num_nodes_visited field
             in (num_nodes_visited, kind :: kinds))
          (num_nodes_visited, []) fields
      in
      num_nodes_visited,
      Pvariant { consts = []; non_consts = [0, List.rev fields] }
    end
  | Tvariant _ ->
    (* CJC XXX this was missing - only caught in 4.14 merge.  Am I missing other
       cases. *)
    num_nodes_visited,
    if Result.is_ok (Ctype.check_type_layout env scty Layout.immediate)
    then Pintval else Pgenval
  | _ ->
    num_nodes_visited, Pgenval

and value_kind_variant env ~visited ~depth ~num_nodes_visited
      (cstrs : Types.constructor_declaration list) rep =
  match rep with
  | Variant_extensible -> assert false
  | Variant_unboxed _ -> begin
      match cstrs with
      | [{cd_args=Cstr_tuple [ty,_]}]
      | [{cd_args=Cstr_record [{ld_type=ty}]}] ->
        value_kind env ~visited ~depth ~num_nodes_visited ty
      | _ -> assert false
    end
  | Variant_boxed layouts ->
    let depth = depth + 1 in
    let for_one_constructor (constructor : Types.constructor_declaration)
          layouts ~depth ~num_nodes_visited =
      let num_nodes_visited = num_nodes_visited + 1 in
      match constructor.cd_args with
      | Cstr_tuple fields ->
        let num_nodes_visited, _, kinds =
          List.fold_left
            (fun (num_nodes_visited, idx, kinds) (ty,_) ->
               let num_nodes_visited = num_nodes_visited + 1 in
               if Layout.equate layouts.(idx) Layout.void then
                 (num_nodes_visited, idx+1, kinds)
               else
                 let num_nodes_visited, kind =
                   value_kind env ~visited ~depth ~num_nodes_visited ty
                 in
                 (num_nodes_visited, idx+1, kind :: kinds))
            (num_nodes_visited, 0, []) fields
        in
        (false, num_nodes_visited), List.rev kinds
      | Cstr_record labels ->
        let is_mutable, num_nodes_visited, _, kinds =
          List.fold_left
            (fun (is_mutable, num_nodes_visited, idx, kinds)
              (label:Types.label_declaration) ->
              let num_nodes_visited = num_nodes_visited + 1 in
              let num_nodes_visited, kinds, field_mutable =
                if Layout.(equate void label.ld_layout)
                then (num_nodes_visited, kinds, Asttypes.Immutable)
                else
                  let (num_nodes_visited, kind) =
                    value_kind env ~visited ~depth ~num_nodes_visited
                      label.ld_type
                  in
                  (num_nodes_visited, kind :: kinds, label.ld_mutable)
              in
              let is_mutable =
                match field_mutable with
                | Mutable -> true
                | Immutable -> is_mutable
              in
              is_mutable, num_nodes_visited, idx+1, kinds)
            (false, num_nodes_visited, 0, []) labels
        in
        (is_mutable, num_nodes_visited), List.rev kinds
    in
    let result =
      List.fold_left (fun (idx,result) constructor ->
        match result with
        | None -> idx+1, None
        | Some (num_nodes_visited,
                next_const, consts, next_tag, non_consts) ->
          let (is_mutable, num_nodes_visited), fields =
            for_one_constructor constructor ~depth ~num_nodes_visited
              layouts.(idx)
          in
          if is_mutable then idx+1, None
          else if List.compare_length_with fields 0 = 0 then
            let consts = next_const :: consts in
            idx+1,
            Some (num_nodes_visited,
                  next_const + 1, consts, next_tag, non_consts)
          else
            let non_consts = (next_tag, fields) :: non_consts in
            idx+1,
            Some (num_nodes_visited,
                  next_const, consts, next_tag + 1, non_consts))
        (0, Some (num_nodes_visited, 0, [], 0, []))
        cstrs
    in
    begin match result with
    | _, None -> (num_nodes_visited, Pgenval)
    | _, Some (num_nodes_visited, _, consts, _, non_consts) ->
      match non_consts with
      | [] -> (num_nodes_visited, Pintval)
      | _::_ ->
        (num_nodes_visited, Pvariant { consts; non_consts })
    end

and value_kind_record env ~visited ~depth ~num_nodes_visited
      (labels : Types.label_declaration list) rep =
  match rep with
  | (Record_unboxed _ | (Record_inlined (_,Variant_unboxed _))) -> begin
      (* Can't be void due to invariant on value_kind *)
      match labels with
      | [{ld_type}] ->
        value_kind env ~visited ~depth ~num_nodes_visited ld_type
      | [] | _ :: _ :: _ -> assert false
    end
  | _ -> begin
      let is_mutable, num_nodes_visited, _, kinds =
        List.fold_left
          (fun (is_mutable, num_nodes_visited, idx, kinds)
            (label:Types.label_declaration) ->
            let num_nodes_visited = num_nodes_visited + 1 in
            let num_nodes_visited, kinds, field_mutable =
              if Layout.(equate void label.ld_layout) then
                (num_nodes_visited, kinds, Asttypes.Immutable)
              else
                let (num_nodes_visited, kind) =
                  value_kind env ~visited ~depth ~num_nodes_visited label.ld_type
                in
                (num_nodes_visited, kind :: kinds, label.ld_mutable)
            in
            let is_mutable =
              match field_mutable with
              | Mutable -> true
              | Immutable -> is_mutable
            in
            is_mutable, num_nodes_visited, idx+1, kinds)
          (false, num_nodes_visited, 0, []) labels
      in
      let kinds = List.rev kinds in
      match is_mutable, kinds with
      | true, _ -> (num_nodes_visited, Pgenval)
      | false, [] -> (num_nodes_visited, Pintval)
      | false, _ :: _ -> begin
          let non_consts =
            match rep with
            | Record_inlined (Ordinary {runtime_tag}, _) ->
              [runtime_tag, kinds]
            | Record_float ->
              [ Obj.double_array_tag,
                List.map (fun _ -> Pfloatval) kinds ]
            | Record_boxed _ ->
              [0, kinds]
            | Record_inlined (Extension _, _) ->
              [0, kinds]
            | Record_unboxed _ -> assert false
          in
          (num_nodes_visited, Pvariant { consts = []; non_consts })
        end
    end

let value_kind env ty =
  let (_num_nodes_visited, value_kind) =
    value_kind env ~visited:Numbers.Int.Set.empty ~depth:0
      ~num_nodes_visited:0 ty
  in
  value_kind

let function_return_value_kind env ty =
  match is_function_type env ty with
  | Some (_lhs, rhs) -> value_kind env rhs
  | None -> Pgenval

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

let maybe_pointer_type env ty = maybe_pointer_type env (scrape_ty env ty)
