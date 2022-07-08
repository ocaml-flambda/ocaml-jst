(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*  Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt  *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Basic operations on core types *)

open Asttypes
open Types

open Local_store

(**** Sets, maps and hashtables of types ****)

module TypeSet = Set.Make(TypeOps)
module TypeMap = Map.Make (TypeOps)
module TypeHash = Hashtbl.Make(TypeOps)

(**** Forward declarations ****)

let print_raw =
  ref (fun _ -> assert false : Format.formatter -> type_expr -> unit)

(**** Type level management ****)

let generic_level = Ident.highest_scope

(* Used to mark a type during a traversal. *)
let lowest_level = Ident.lowest_scope
let pivot_level = 2 * lowest_level - 1
    (* pivot_level - lowest_level < lowest_level *)

(**** Some type creators ****)

let new_id = s_ref (-1)

let newty2 level desc  =
  incr new_id; { desc; level; scope = lowest_level; id = !new_id }
let newgenty desc      = newty2 generic_level desc
let newgenvar ?name () = newgenty (Tvar name)
(*
let newmarkedvar level =
  incr new_id; { desc = Tvar; level = pivot_level - level; id = !new_id }
let newmarkedgenvar () =
  incr new_id;
  { desc = Tvar; level = pivot_level - generic_level; id = !new_id }
*)

(**** Check some types ****)

let is_Tvar = function {desc=Tvar _} -> true | _ -> false
let is_Tunivar = function {desc=Tunivar _} -> true | _ -> false
let is_Tconstr = function {desc=Tconstr _} -> true | _ -> false

let dummy_method = "*dummy method*"

(**** Definitions for backtracking ****)

type change =
    Ctype : type_expr * type_desc -> change
  | Ccompress : type_expr * type_desc * type_desc -> change
  | Clevel : type_expr * int -> change
  | Cscope : type_expr * int -> change
  | Cname :
      (Path.t * type_expr list) option ref * (Path.t * type_expr list) option -> change
  | Crow : row_field option ref * row_field option -> change
  | Ckind : field_kind option ref * field_kind option -> change
  | Ccommu : commutable ref * commutable -> change
  | Cuniv : type_expr option ref * type_expr option -> change
  | Ctypeset : TypeSet.t ref * TypeSet.t -> change
  | Cmode_upper : 'a mode_var * 'a -> change
  | Cmode_lower : 'a mode_var * 'a -> change
  | Cmode_vlower : 'a mode_var * 'a mode_var list -> change

type changes =
    Change of change * changes ref
  | Unchanged
  | Invalid

let trail = s_table Weak.create 1

let log_change ch =
  match Weak.get !trail 0 with None -> ()
  | Some r ->
      let r' = ref Unchanged in
      r := Change (ch, r');
      Weak.set !trail 0 (Some r')

let log_changes chead ctail =
  if chead = Unchanged then (assert (!ctail = Unchanged))
  else match Weak.get !trail 0 with None -> ()
  | Some r ->
      r := chead;
      Weak.set !trail 0 (Some ctail)

let append_change ctail ch =
  assert (!(!ctail) = Unchanged);
  let r' = ref Unchanged in
  (!ctail) := Change (ch, r');
  ctail := r'

(**** Representative of a type ****)

let rec field_kind_repr =
  function
    Fvar {contents = Some kind} -> field_kind_repr kind
  | kind                        -> kind

let rec repr_link compress t d =
 function
   {desc = Tlink t' as d'} ->
     repr_link true t d' t'
 | {desc = Tfield (_, k, _, t') as d'} when field_kind_repr k = Fabsent ->
     repr_link true t d' t'
 | t' ->
     if compress then begin
       log_change (Ccompress (t, t.desc, d)); t.desc <- d
     end;
     t'

let repr t =
  match t.desc with
   Tlink t' as d ->
     repr_link false t d t'
 | Tfield (_, k, _, t') as d when field_kind_repr k = Fabsent ->
     repr_link false t d t'
 | _ -> t

let rec commu_repr = function
    Clink r when !r <> Cunknown -> commu_repr !r
  | c -> c

let rec row_field_repr_aux tl = function
    Reither(_, tl', _, {contents = Some fi}) ->
      row_field_repr_aux (tl@tl') fi
  | Reither(c, tl', m, r) ->
      Reither(c, tl@tl', m, r)
  | Rpresent (Some _) when tl <> [] ->
      Rpresent (Some (List.hd tl))
  | fi -> fi

let row_field_repr fi = row_field_repr_aux [] fi

let rec rev_concat l ll =
  match ll with
    [] -> l
  | l'::ll -> rev_concat (l'@l) ll

let rec row_repr_aux ll row =
  match (repr row.row_more).desc with
  | Tvariant row' ->
      let f = row.row_fields in
      row_repr_aux (if f = [] then ll else f::ll) row'
  | _ ->
      if ll = [] then row else
      {row with row_fields = rev_concat row.row_fields ll}

let row_repr row = row_repr_aux [] row

let rec row_field tag row =
  let rec find = function
    | (tag',f) :: fields ->
        if tag = tag' then row_field_repr f else find fields
    | [] ->
        match repr row.row_more with
        | {desc=Tvariant row'} -> row_field tag row'
        | _ -> Rabsent
  in find row.row_fields

let rec row_more row =
  match repr row.row_more with
  | {desc=Tvariant row'} -> row_more row'
  | ty -> ty

let merge_fixed_explanation fixed1 fixed2 =
  match fixed1, fixed2 with
  | Some Univar _ as x, _ | _, (Some Univar _ as x) -> x
  | Some Fixed_private as x, _ | _, (Some Fixed_private as x) -> x
  | Some Reified _ as x, _ | _, (Some Reified _ as x) -> x
  | Some Rigid as x, _ | _, (Some Rigid as x) -> x
  | None, None -> None


let fixed_explanation row =
  let row = row_repr row in
  match row.row_fixed with
  | Some _ as x -> x
  | None ->
      let more = repr row.row_more in
      match more.desc with
      | Tvar _ | Tnil -> None
      | Tunivar _ -> Some (Univar more)
      | Tconstr (p,_,_) -> Some (Reified p)
      | _ -> assert false

let is_fixed row = match row.row_fixed with
  | None -> false
  | Some _ -> true

let row_fixed row = fixed_explanation row <> None


let static_row row =
  let row = row_repr row in
  row.row_closed &&
  List.for_all
    (fun (_,f) -> match row_field_repr f with Reither _ -> false | _ -> true)
    row.row_fields

let hash_variant s =
  let accu = ref 0 in
  for i = 0 to String.length s - 1 do
    accu := 223 * !accu + Char.code s.[i]
  done;
  (* reduce to 31 bits *)
  accu := !accu land (1 lsl 31 - 1);
  (* make it signed for 64 bits architectures *)
  if !accu > 0x3FFFFFFF then !accu - (1 lsl 31) else !accu

let proxy ty =
  let ty0 = repr ty in
  match ty0.desc with
  | Tvariant row when not (static_row row) ->
      row_more row
  | Tobject (ty, _) ->
      let rec proxy_obj ty =
        match ty.desc with
          Tfield (_, _, _, ty) | Tlink ty -> proxy_obj ty
        | Tvar _ | Tunivar _ | Tconstr _ -> ty
        | Tnil -> ty0
        | _ -> assert false
      in proxy_obj ty
  | _ -> ty0

(**** Utilities for fixed row private types ****)

let row_of_type t =
  match (repr t).desc with
    Tobject(t,_) ->
      let rec get_row t =
        let t = repr t in
        match t.desc with
          Tfield(_,_,_,t) -> get_row t
        | _ -> t
      in get_row t
  | Tvariant row ->
      row_more row
  | _ ->
      t

let has_constr_row t =
  not (is_Tconstr t) && is_Tconstr (row_of_type t)

let is_row_name s =
  let l = String.length s in
  if l < 4 then false else String.sub s (l-4) 4 = "#row"

let is_constr_row ~allow_ident t =
  match t.desc with
    Tconstr (Path.Pident id, _, _) when allow_ident ->
      is_row_name (Ident.name id)
  | Tconstr (Path.Pdot (_, s), _, _) -> is_row_name s
  | _ -> false


                  (**********************************)
                  (*  Utilities for type traversal  *)
                  (**********************************)

let rec fold_row f init row =
  let result =
    List.fold_left
      (fun init (_, fi) ->
         match row_field_repr fi with
         | Rpresent(Some ty) -> f init ty
         | Reither(_, tl, _, _) -> List.fold_left f init tl
         | _ -> init)
      init
      row.row_fields
  in
  match (repr row.row_more).desc with
    Tvariant row -> fold_row f result row
  | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
    begin match
      Option.map (fun (_,l) -> List.fold_left f result l) row.row_name
    with
    | None -> result
    | Some result -> result
    end
  | _ -> assert false

let iter_row f row =
  fold_row (fun () v -> f v) () row

let fold_type_expr f init ty =
  match ty.desc with
    Tvar _              -> init
  | Tarrow (_, ty1, ty2, _) ->
    let result = f init ty1 in
    f result ty2
  | Ttuple l            -> List.fold_left f init l
  | Tconstr (_, l, _)   -> List.fold_left f init l
  | Tobject(ty, {contents = Some (_, p)})
    ->
    let result = f init ty in
    List.fold_left f result p
  | Tobject (ty, _)     -> f init ty
  | Tvariant row        ->
    let result = fold_row f init row in
    f result (row_more row)
  | Tfield (_, _, ty1, ty2) ->
    let result = f init ty1 in
    f result ty2
  | Tnil                -> init
  | Tlink ty            -> f init ty
  | Tsubst ty           -> f init ty
  | Tunivar _           -> init
  | Tpoly (ty, tyl)     ->
    let result = f init ty in
    List.fold_left f result tyl
  | Tpackage (_, _, l)  -> List.fold_left f init l

let iter_type_expr f ty =
  fold_type_expr (fun () v -> f v) () ty

let rec iter_abbrev f = function
    Mnil                   -> ()
  | Mcons(_, _, ty, ty', rem) -> f ty; f ty'; iter_abbrev f rem
  | Mlink rem              -> iter_abbrev f !rem

type type_iterators =
  { it_signature: type_iterators -> signature -> unit;
    it_signature_item: type_iterators -> signature_item -> unit;
    it_value_description: type_iterators -> value_description -> unit;
    it_type_declaration: type_iterators -> type_declaration -> unit;
    it_extension_constructor: type_iterators -> extension_constructor -> unit;
    it_module_declaration: type_iterators -> module_declaration -> unit;
    it_modtype_declaration: type_iterators -> modtype_declaration -> unit;
    it_class_declaration: type_iterators -> class_declaration -> unit;
    it_class_type_declaration: type_iterators -> class_type_declaration -> unit;
    it_functor_param: type_iterators -> functor_parameter -> unit;
    it_module_type: type_iterators -> module_type -> unit;
    it_class_type: type_iterators -> class_type -> unit;
    it_type_kind: type_iterators -> type_kind -> unit;
    it_do_type_expr: type_iterators -> type_expr -> unit;
    it_type_expr: type_iterators -> type_expr -> unit;
    it_path: Path.t -> unit; }

let iter_type_expr_cstr_args f = function
  | Cstr_tuple tl -> List.iter f tl
  | Cstr_record lbls -> List.iter (fun d -> f d.ld_type) lbls

let map_type_expr_cstr_args f = function
  | Cstr_tuple tl -> Cstr_tuple (List.map f tl)
  | Cstr_record lbls ->
      Cstr_record (List.map (fun d -> {d with ld_type=f d.ld_type}) lbls)

let iter_type_expr_kind f = function
  | Type_abstract -> ()
  | Type_variant cstrs ->
      List.iter
        (fun cd ->
           iter_type_expr_cstr_args f cd.cd_args;
           Option.iter f cd.cd_res
        )
        cstrs
  | Type_record(lbls, _) ->
      List.iter (fun d -> f d.ld_type) lbls
  | Type_open ->
      ()


let type_iterators =
  let it_signature it =
    List.iter (it.it_signature_item it)
  and it_signature_item it = function
      Sig_value (_, vd, _)          -> it.it_value_description it vd
    | Sig_type (_, td, _, _)        -> it.it_type_declaration it td
    | Sig_typext (_, td, _, _)      -> it.it_extension_constructor it td
    | Sig_module (_, _, md, _, _)   -> it.it_module_declaration it md
    | Sig_modtype (_, mtd, _)       -> it.it_modtype_declaration it mtd
    | Sig_class (_, cd, _, _)       -> it.it_class_declaration it cd
    | Sig_class_type (_, ctd, _, _) -> it.it_class_type_declaration it ctd
  and it_value_description it vd =
    it.it_type_expr it vd.val_type
  and it_type_declaration it td =
    List.iter (it.it_type_expr it) td.type_params;
    Option.iter (it.it_type_expr it) td.type_manifest;
    it.it_type_kind it td.type_kind
  and it_extension_constructor it td =
    it.it_path td.ext_type_path;
    List.iter (it.it_type_expr it) td.ext_type_params;
    iter_type_expr_cstr_args (it.it_type_expr it) td.ext_args;
    Option.iter (it.it_type_expr it) td.ext_ret_type
  and it_module_declaration it md =
    it.it_module_type it md.md_type
  and it_modtype_declaration it mtd =
    Option.iter (it.it_module_type it) mtd.mtd_type
  and it_class_declaration it cd =
    List.iter (it.it_type_expr it) cd.cty_params;
    it.it_class_type it cd.cty_type;
    Option.iter (it.it_type_expr it) cd.cty_new;
    it.it_path cd.cty_path
  and it_class_type_declaration it ctd =
    List.iter (it.it_type_expr it) ctd.clty_params;
    it.it_class_type it ctd.clty_type;
    it.it_path ctd.clty_path
  and it_functor_param it = function
    | Unit -> ()
    | Named (_, mt) -> it.it_module_type it mt
  and it_module_type it = function
      Mty_ident p
    | Mty_alias p -> it.it_path p
    | Mty_signature sg -> it.it_signature it sg
    | Mty_functor (p, mt) ->
        it.it_functor_param it p;
        it.it_module_type it mt
  and it_class_type it = function
      Cty_constr (p, tyl, cty) ->
        it.it_path p;
        List.iter (it.it_type_expr it) tyl;
        it.it_class_type it cty
    | Cty_signature cs ->
        it.it_type_expr it cs.csig_self;
        Vars.iter (fun _ (_,_,ty) -> it.it_type_expr it ty) cs.csig_vars;
        List.iter
          (fun (p, tl) -> it.it_path p; List.iter (it.it_type_expr it) tl)
          cs.csig_inher
    | Cty_arrow  (_, ty, cty) ->
        it.it_type_expr it ty;
        it.it_class_type it cty
  and it_type_kind it kind =
    iter_type_expr_kind (it.it_type_expr it) kind
  and it_do_type_expr it ty =
    iter_type_expr (it.it_type_expr it) ty;
    match ty.desc with
      Tconstr (p, _, _)
    | Tobject (_, {contents=Some (p, _)})
    | Tpackage (p, _, _) ->
        it.it_path p
    | Tvariant row ->
        Option.iter (fun (p,_) -> it.it_path p) (row_repr row).row_name
    | _ -> ()
  and it_path _p = ()
  in
  { it_path; it_type_expr = it_do_type_expr; it_do_type_expr;
    it_type_kind; it_class_type; it_functor_param; it_module_type;
    it_signature; it_class_type_declaration; it_class_declaration;
    it_modtype_declaration; it_module_declaration; it_extension_constructor;
    it_type_declaration; it_value_description; it_signature_item; }

let copy_row f fixed row keep more =
  let fields = List.map
      (fun (l, fi) -> l,
        match row_field_repr fi with
        | Rpresent(Some ty) -> Rpresent(Some(f ty))
        | Reither(c, tl, m, e) ->
            let e = if keep then e else ref None in
            let m = if is_fixed row then fixed else m in
            let tl = List.map f tl in
            Reither(c, tl, m, e)
        | _ -> fi)
      row.row_fields in
  let name =
    match row.row_name with
    | None -> None
    | Some (path, tl) -> Some (path, List.map f tl) in
  let row_fixed = if fixed then row.row_fixed else None in
  { row_fields = fields; row_more = more;
    row_bound = (); row_fixed;
    row_closed = row.row_closed; row_name = name; }

let rec copy_kind = function
    Fvar{contents = Some k} -> copy_kind k
  | Fvar _   -> Fvar (ref None)
  | Fpresent -> Fpresent
  | Fabsent  -> assert false

let copy_commu c =
  if commu_repr c = Cok then Cok else Clink (ref Cunknown)

(* Since univars may be used as row variables, we need to do some
   encoding during substitution *)
let rec norm_univar ty =
  match ty.desc with
    Tunivar _ | Tsubst _ -> ty
  | Tlink ty           -> norm_univar ty
  | Ttuple (ty :: _)   -> norm_univar ty
  | _                  -> assert false

let rec copy_type_desc ?(keep_names=false) f = function
    Tvar _ as ty        -> if keep_names then ty else Tvar None
  | Tarrow (p, ty1, ty2, c)-> Tarrow (p, f ty1, f ty2, copy_commu c)
  | Ttuple l            -> Ttuple (List.map f l)
  | Tconstr (p, l, _)   -> Tconstr (p, List.map f l, ref Mnil)
  | Tobject(ty, {contents = Some (p, tl)})
                        -> Tobject (f ty, ref (Some(p, List.map f tl)))
  | Tobject (ty, _)     -> Tobject (f ty, ref None)
  | Tvariant _          -> assert false (* too ambiguous *)
  | Tfield (p, k, ty1, ty2) -> (* the kind is kept shared *)
      Tfield (p, field_kind_repr k, f ty1, f ty2)
  | Tnil                -> Tnil
  | Tlink ty            -> copy_type_desc f ty.desc
  | Tsubst _            -> assert false
  | Tunivar _ as ty     -> ty (* always keep the name *)
  | Tpoly (ty, tyl)     ->
      let tyl = List.map (fun x -> norm_univar (f x)) tyl in
      Tpoly (f ty, tyl)
  | Tpackage (p, n, l)  -> Tpackage (p, n, List.map f l)

(* Utilities for copying *)

module For_copy : sig
  type copy_scope

  val save_desc: copy_scope -> type_expr -> type_desc -> unit

  val dup_kind: copy_scope -> field_kind option ref -> unit

  val with_scope: (copy_scope -> 'a) -> 'a
end = struct
  type copy_scope = {
    mutable saved_desc : (type_expr * type_desc) list;
    (* Save association of generic nodes with their description. *)

    mutable saved_kinds: field_kind option ref list;
    (* duplicated kind variables *)

    mutable new_kinds  : field_kind option ref list;
    (* new kind variables *)
  }

  let save_desc copy_scope ty desc =
    copy_scope.saved_desc <- (ty, desc) :: copy_scope.saved_desc

  let dup_kind copy_scope r =
    assert (Option.is_none !r);
    if not (List.memq r copy_scope.new_kinds) then begin
      copy_scope.saved_kinds <- r :: copy_scope.saved_kinds;
      let r' = ref None in
      copy_scope.new_kinds <- r' :: copy_scope.new_kinds;
      r := Some (Fvar r')
    end

  (* Restore type descriptions. *)
  let cleanup { saved_desc; saved_kinds; _ } =
    List.iter (fun (ty, desc) -> ty.desc <- desc) saved_desc;
    List.iter (fun r -> r := None) saved_kinds

  let with_scope f =
    let scope = { saved_desc = []; saved_kinds = []; new_kinds = [] } in
    let res = f scope in
    cleanup scope;
    res
end

(* Mark a type. *)
let rec mark_type ty =
  let ty = repr ty in
  if ty.level >= lowest_level then begin
    ty.level <- pivot_level - ty.level;
    iter_type_expr mark_type ty
  end

let mark_type_node ty =
  let ty = repr ty in
  if ty.level >= lowest_level then begin
    ty.level <- pivot_level - ty.level;
  end

let mark_type_params ty =
  iter_type_expr mark_type ty

let type_iterators =
  let it_type_expr it ty =
    let ty = repr ty in
    if ty.level >= lowest_level then begin
      mark_type_node ty;
      it.it_do_type_expr it ty;
    end
  in
  {type_iterators with it_type_expr}


(* Remove marks from a type. *)
let rec unmark_type ty =
  let ty = repr ty in
  if ty.level < lowest_level then begin
    ty.level <- pivot_level - ty.level;
    iter_type_expr unmark_type ty
  end

let unmark_iterators =
  let it_type_expr _it ty = unmark_type ty in
  {type_iterators with it_type_expr}

let unmark_type_decl decl =
  unmark_iterators.it_type_declaration unmark_iterators decl

let unmark_extension_constructor ext =
  List.iter unmark_type ext.ext_type_params;
  iter_type_expr_cstr_args unmark_type ext.ext_args;
  Option.iter unmark_type ext.ext_ret_type

let unmark_class_signature sign =
  unmark_type sign.csig_self;
  Vars.iter (fun _l (_m, _v, t) -> unmark_type t) sign.csig_vars

let unmark_class_type cty =
  unmark_iterators.it_class_type unmark_iterators cty


                  (*******************************************)
                  (*  Memorization of abbreviation expansion *)
                  (*******************************************)

(* Search whether the expansion has been memorized. *)

let lte_public p1 p2 =  (* Private <= Public *)
  match p1, p2 with
  | Private, _ | _, Public -> true
  | Public, Private -> false

let rec find_expans priv p1 = function
    Mnil -> None
  | Mcons (priv', p2, _ty0, ty, _)
    when lte_public priv priv' && Path.same p1 p2 -> Some ty
  | Mcons (_, _, _, _, rem)   -> find_expans priv p1 rem
  | Mlink {contents = rem} -> find_expans priv p1 rem

(* debug: check for cycles in abbreviation. only works with -principal
let rec check_expans visited ty =
  let ty = repr ty in
  assert (not (List.memq ty visited));
  match ty.desc with
    Tconstr (path, args, abbrev) ->
      begin match find_expans path !abbrev with
        Some ty' -> check_expans (ty :: visited) ty'
      | None -> ()
      end
  | _ -> ()
*)

let memo = s_ref []
        (* Contains the list of saved abbreviation expansions. *)

let cleanup_abbrev () =
        (* Remove all memorized abbreviation expansions. *)
  List.iter (fun abbr -> abbr := Mnil) !memo;
  memo := []

let memorize_abbrev mem priv path v v' =
        (* Memorize the expansion of an abbreviation. *)
  mem := Mcons (priv, path, v, v', !mem);
  (* check_expans [] v; *)
  memo := mem :: !memo

let rec forget_abbrev_rec mem path =
  match mem with
    Mnil ->
      mem
  | Mcons (_, path', _, _, rem) when Path.same path path' ->
      rem
  | Mcons (priv, path', v, v', rem) ->
      Mcons (priv, path', v, v', forget_abbrev_rec rem path)
  | Mlink mem' ->
      mem' := forget_abbrev_rec !mem' path;
      raise Exit

let forget_abbrev mem path =
  try mem := forget_abbrev_rec !mem path with Exit -> ()

(* debug: check for invalid abbreviations
let rec check_abbrev_rec = function
    Mnil -> true
  | Mcons (_, ty1, ty2, rem) ->
      repr ty1 != repr ty2
  | Mlink mem' ->
      check_abbrev_rec !mem'

let check_memorized_abbrevs () =
  List.for_all (fun mem -> check_abbrev_rec !mem) !memo
*)

                  (**********************************)
                  (*  Utilities for labels          *)
                  (**********************************)

let is_optional = function Optional _ -> true | _ -> false

let label_name = function
    Nolabel -> ""
  | Labelled s
  | Optional s -> s

let prefixed_label_name = function
    Nolabel -> ""
  | Labelled s -> "~" ^ s
  | Optional s -> "?" ^ s

let rec extract_label_aux hd l = function
  | [] -> None
  | (l',t as p) :: ls ->
      if label_name l' = l then
        Some (l', t, hd <> [], List.rev_append hd ls)
      else
        extract_label_aux (p::hd) l ls

let extract_label l ls = extract_label_aux [] l ls


                  (**********************************)
                  (*  Utilities for backtracking    *)
                  (**********************************)

let undo_change = function
    Ctype  (ty, desc) -> ty.desc <- desc
  | Ccompress  (ty, desc, _) -> ty.desc <- desc
  | Clevel (ty, level) -> ty.level <- level
  | Cscope (ty, scope) -> ty.scope <- scope
  | Cname  (r, v) -> r := v
  | Crow   (r, v) -> r := v
  | Ckind  (r, v) -> r := v
  | Ccommu (r, v) -> r := v
  | Cuniv  (r, v) -> r := v
  | Ctypeset (r, v) -> r := v
  | Cmode_upper (v, u) -> v.upper <- u
  | Cmode_lower (v, l) -> v.lower <- l
  | Cmode_vlower (v, vs) -> v.vlower <- vs

type snapshot = changes ref * int
let last_snapshot = s_ref 0

let log_type ty =
  if ty.id <= !last_snapshot then log_change (Ctype (ty, ty.desc))
let link_type ty ty' =
  log_type ty;
  let desc = ty.desc in
  ty.desc <- Tlink ty';
  (* Name is a user-supplied name for this unification variable (obtained
   * through a type annotation for instance). *)
  match desc, ty'.desc with
    Tvar name, Tvar name' ->
      begin match name, name' with
      | Some _, None ->  log_type ty'; ty'.desc <- Tvar name
      | None, Some _ ->  ()
      | Some _, Some _ ->
          if ty.level < ty'.level then (log_type ty'; ty'.desc <- Tvar name)
      | None, None   ->  ()
      end
  | _ -> ()
  (* ; assert (check_memorized_abbrevs ()) *)
  (*  ; check_expans [] ty' *)
let set_type_desc ty td =
  if td != ty.desc then begin
    log_type ty;
    ty.desc <- td
  end
let set_level ty level =
  if level <> ty.level then begin
    if ty.id <= !last_snapshot then log_change (Clevel (ty, ty.level));
    ty.level <- level
  end
let set_scope ty scope =
  if scope <> ty.scope then begin
    if ty.id <= !last_snapshot then log_change (Cscope (ty, ty.scope));
    ty.scope <- scope
  end
let set_univar rty ty =
  log_change (Cuniv (rty, !rty)); rty := Some ty
let set_name nm v =
  log_change (Cname (nm, !nm)); nm := v
let set_row_field e v =
  log_change (Crow (e, !e)); e := Some v
let set_kind rk k =
  log_change (Ckind (rk, !rk)); rk := Some k
let set_commu rc c =
  log_change (Ccommu (rc, !rc)); rc := c
let set_typeset rs s =
  log_change (Ctypeset (rs, !rs)); rs := s

let snapshot () =
  let old = !last_snapshot in
  last_snapshot := !new_id;
  match Weak.get !trail 0 with Some r -> (r, old)
  | None ->
      let r = ref Unchanged in
      Weak.set !trail 0 (Some r);
      (r, old)

let rec rev_log accu = function
    Unchanged -> accu
  | Invalid -> assert false
  | Change (ch, next) ->
      let d = !next in
      next := Invalid;
      rev_log (ch::accu) d

let backtrack (changes, old) =
  match !changes with
    Unchanged -> last_snapshot := old
  | Invalid -> failwith "Btype.backtrack"
  | Change _ as change ->
      cleanup_abbrev ();
      let backlog = rev_log [] change in
      List.iter undo_change backlog;
      changes := Unchanged;
      last_snapshot := old;
      Weak.set !trail 0 (Some changes)

let rec rev_compress_log log r =
  match !r with
    Unchanged | Invalid ->
      log
  | Change (Ccompress _, next) ->
      rev_compress_log (r::log) next
  | Change (_, next) ->
      rev_compress_log log next

let undo_compress (changes, _old) =
  match !changes with
    Unchanged
  | Invalid -> ()
  | Change _ ->
      let log = rev_compress_log [] changes in
      List.iter
        (fun r -> match !r with
          Change (Ccompress (ty, desc, d), next) when ty.desc == d ->
            ty.desc <- desc; r := !next
        | _ -> ())
        log

module type Lattice_mode = sig
  type const
  val min_const : const
  val max_const : const
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
end

module Lattice_solver (L : Lattice_mode) = struct
  exception NotSubmode

  let set_lower ~log v lower =
    append_change log (Cmode_lower (v, v.lower));
    v.lower <- lower

  let set_upper ~log v upper =
    append_change log (Cmode_upper (v, v.upper));
    v.upper <- upper

  let set_vlower ~log v vlower =
    append_change log (Cmode_vlower (v, v.vlower));
    v.vlower <- vlower

  let submode_cv ~log m v =
    (* Printf.printf "  %a <= %a\n" pp_c m pp_v v; *)
    if L.le_const m v.lower then ()
    else if not (L.le_const m v.upper) then raise NotSubmode
    else begin
      let m = L.join_const v.lower m in
      set_lower ~log v m;
      if m = v.upper then set_vlower ~log v []
    end

  let rec submode_vc ~log v m =
    (* Printf.printf "  %a <= %a\n" pp_v v pp_c m; *)
    if L.le_const v.upper m then ()
    else if not (L.le_const v.lower m) then raise NotSubmode
    else begin
      let m = L.meet_const v.upper m in
      set_upper ~log v m;
      v.vlower |> List.iter (fun a ->
        (* a <= v <= m *)
        submode_vc ~log a m;
        set_lower ~log v (L.join_const v.lower a.lower);
      );
      if v.lower = m then set_vlower ~log v []
    end

  let submode_vv ~log a b =
    (* Printf.printf "  %a <= %a\n" pp_v a pp_v b; *)
    if L.le_const a.upper b.lower then ()
    else if a == b || List.memq a b.vlower then ()
    else begin
      submode_vc ~log a b.upper;
      set_vlower ~log b (a :: b.vlower);
      submode_cv ~log a.lower b;
    end

  let submode a b =
    let log_head = ref Unchanged in
    let log = ref log_head in
    match
      match a, b with
      | Amode a, Amode b ->
         if not (L.le_const a b) then raise NotSubmode
      | Amodevar v, Amode c ->
         (* Printf.printf "%a <= %a\n" pp_v v pp_c c; *)
         submode_vc ~log v c
      | Amode c, Amodevar v ->
         (* Printf.printf "%a <= %a\n" pp_c c pp_v v; *)
         submode_cv ~log c v
      | Amodevar a, Amodevar b ->
         (* Printf.printf "%a <= %a\n" pp_v a pp_v b; *)
         submode_vv ~log a b
    with
    | () ->
       log_changes !log_head !log;
       Ok ()
    | exception NotSubmode ->
       let backlog = rev_log [] !log_head in
       List.iter undo_change backlog;
       Error ()

  let submode_exn t1 t2 =
    match submode t1 t2 with
    | Ok () -> ()
    | Error () -> invalid_arg "submode_exn"

  let equate a b =
    match submode a b, submode b a with
    | Ok (), Ok () -> Ok ()
    | Error (), _ | _, Error () -> Error ()

  let constrain_upper = function
    | Amode m -> m
    | Amodevar v ->
       submode_exn (Amode v.upper) (Amodevar v);
       v.upper

  let next_id = ref (-1)
  let fresh () =
    incr next_id;
    { upper = L.max_const;
      lower = L.min_const;
      vlower = [];
      mvid = !next_id;
      mark = false }

  let rec all_equal v = function
    | [] -> true
    | v' :: rest ->
      if v == v' then all_equal v rest
      else false

  let joinvars vars =
    match vars with
    | [] -> Amode L.min_const
    | v :: rest ->
      let v =
        if all_equal v rest then v
        else begin
          let v = fresh () in
          List.iter (fun v' -> submode_exn (Amodevar v') (Amodevar v)) vars;
          v
        end
      in
      Amodevar v

  exception Became_constant
  let compress_vlower v =
    let nmarked = ref 0 in
    let mark v' =
      assert (not v'.mark);
      v'.mark <- true;
      incr nmarked
    in
    let unmark v' =
      assert v'.mark;
      v'.mark <- false;
      decr nmarked
    in
    let new_lower = ref v.lower in
    let new_vlower = ref v.vlower in
    (* Ensure that each transitive lower bound of v
       is a direct lower bound of v *)
    let rec trans v' =
      if L.le_const v'.upper !new_lower then ()
      else if v'.mark then ()
      else begin
        mark v';
        new_vlower := v' :: !new_vlower;
        trans_low v'
      end
    and trans_low v' =
      assert (v != v');
      if not (L.le_const v'.lower v.upper) then
        Misc.fatal_error "compress_vlower: invalid bounds";
      if not (L.le_const v'.lower !new_lower) then begin
        new_lower := L.join_const !new_lower v'.lower;
        if !new_lower = v.upper then
          (* v is now a constant, no need to keep computing bounds *)
          raise Became_constant
      end;
      List.iter trans v'.vlower
    in
    mark v;
    List.iter mark v.vlower;
    let became_constant =
      match List.iter trans_low v.vlower with
      | () -> false
      | exception Became_constant -> true
    in
    List.iter unmark !new_vlower;
    unmark v;
    assert (!nmarked = 0);
    if became_constant then new_vlower := [];
    if !new_lower != v.lower || !new_vlower != v.vlower then begin
      let log_head = ref Unchanged in
      let log = ref log_head in
      set_lower ~log v !new_lower;
      set_vlower ~log v !new_vlower;
      log_changes !log_head !log;
    end

  let constrain_lower = function
    | Amode m -> m
    | Amodevar v ->
        compress_vlower v;
        submode_exn (Amodevar v) (Amode v.lower);
        v.lower

  let check_const = function
    | Amode m -> Some m
    | Amodevar v ->
      compress_vlower v;
      if v.lower = v.upper then Some v.lower else None

  let print_var_id ppf v =
    Format.fprintf ppf "?%i" v.mvid

  let print_var ppf v =
    compress_vlower v;
    if v.lower = v.upper then begin
      L.print_const ppf v.lower
    end else if v.vlower = [] then begin
      print_var_id ppf v
    end else begin
      Format.fprintf ppf "%a[> %a]"
        print_var_id v
        (Format.pp_print_list print_var_id) v.vlower
    end

  let print ppf = function
    | Amode m -> L.print_const ppf m
    | Amodevar v -> print_var ppf v
end

module Locality_mode = struct
  module T = struct
    type const = Types.locality = Global | Local

    let min_const = Global
    let max_const = Local

    let le_const a b =
      match a, b with
      | Global, _ | _, Local -> true
      | Local, Global -> false

    let join_const a b =
      match a, b with
      | Local, _ | _, Local -> Local
      | Global, Global -> Global

    let meet_const a b =
      match a, b with
      | Global, _ | _, Global -> Global
      | Local, Local -> Local

    let print_const ppf = function
      | Global -> Format.fprintf ppf "Global"
      | Local -> Format.fprintf ppf "Local"
  end
  include T
  include Lattice_solver(T)

  let global = Amode Global
  let local = Amode Local
  let max_mode = local
  let min_mode = global

  let of_const = function
    | Global -> global
    | Local -> local

  let join ms =
    let rec aux vars = function
      | [] -> joinvars vars
      | Amode Global :: ms -> aux vars ms
      | Amode Local :: _ -> Amode Local
      | Amodevar v :: ms -> aux (v :: vars) ms
    in aux [] ms

  let newvar () = Amodevar (fresh ())

  let newvar_below = function
    | Amode Global -> Amode Global, false
    | m ->
      let v = newvar () in
      submode_exn v m;
      v, true

  let newvar_above = function
    | Amode Local -> Amode Local, false
    | m ->
      let v = newvar () in
      submode_exn m v;
      v, true
end

module Uniqueness_mode = struct
  module T = struct
    type const = Types.uniqueness = Unique | Shared

    let min_const = Unique
    let max_const = Shared

    let le_const a b =
      match a, b with
      | Unique, _ | _, Shared -> true
      | Shared, Unique -> false

    let join_const a b =
      match a, b with
      | Shared, _ | _, Shared -> Shared
      | Unique, Unique -> Unique

    let meet_const a b =
      match a, b with
      | Unique, _ | _, Unique -> Unique
      | Shared, Shared -> Shared

    let print_const ppf = function
      | Shared -> Format.fprintf ppf "Shared"
      | Unique -> Format.fprintf ppf "Unique"
  end
  include T
  include Lattice_solver(T)

  let unique = Amode Unique
  let shared = Amode Shared
  let max_mode = shared
  let min_mode = unique

  let of_const = function
    | Unique -> unique
    | Shared -> shared

  (* let join ms =
   *   let rec aux vars = function
   *     | [] -> joinvars vars
   *     | Amode Unique :: ms -> aux vars ms
   *     | Amode Shared :: _ -> Amode Shared
   *     | Amodevar v :: ms -> aux (v :: vars) ms
   *   in aux [] ms *)

  (* let newvar () = Amodevar (fresh ())
   *
   * let newvar_below = function
   *   | Amode Unique -> Amode Unique, false
   *   | m ->
   *     let v = newvar () in
   *     submode_exn v m;
   *     v, true
   *
   * let newvar_above = function
   *   | Amode Shared -> Amode Shared, false
   *   | m ->
   *     let v = newvar () in
   *     submode_exn m v;
   *     v, true *)
end

module Alloc_mode = struct
  (* Modes are ordered so that [global] is a submode of [local] *)
  type locality = Types.locality = Global | Local
  (* Modes are ordered so that [unique] is a submode of [shared] *)
  type uniqueness = Types.uniqueness = Unique | Shared
  type const = locality * uniqueness
  type t = Types.alloc_mode

  let of_const (l, u) = { locality = Locality_mode.of_const l; uniqueness = Uniqueness_mode.of_const u }

  let global = of_const (Global, Shared)
  let local = of_const (Local, Shared)
  let unique = of_const (Global, Unique)
  let local_unique = of_const (Local, Unique)

  let min_mode = global (* TODO unique *)

  let max_mode = local

  type error = [`Locality | `Uniqueness]

  let submode {locality = l1; uniqueness = u1} {locality = l2; uniqueness = u2} =
    match Locality_mode.submode l1 l2 with
      | Ok () -> begin match Uniqueness_mode.submode u1 u2 with
        | Ok () -> Ok ()
        | Error () -> Error `Uniqueness
        end
      | Error () -> Error `Locality

  let submode_exn {locality = l1; uniqueness = u1} {locality = l2; uniqueness = u2} =
    Locality_mode.submode_exn l1 l2;
    Uniqueness_mode.submode_exn u1 u2

  let equate {locality = l1; uniqueness = u1} {locality = l2; uniqueness = u2} =
    match Locality_mode.equate l1 l2 with
    | Ok () -> begin match Uniqueness_mode.equate u1 u2 with
      | Ok () -> Ok ()
      | Error () -> Error `Uniqueness
    end
    | Error () -> Error `Locality

  let join_const (l1, _u1) (l2, _u2) = (Locality_mode.join_const l1 l2, Shared)

  let join ms =
    { locality = Locality_mode.join (List.map (fun t -> t.locality) ms);
      uniqueness = Amode Shared }

  let constrain_upper {locality; uniqueness = _} =
    Locality_mode.constrain_upper locality, Shared
  (* Uniqueness_mode.constrain_upper uniqueness *)

  let constrain_lower {locality; uniqueness = _} =
    Locality_mode.constrain_lower locality, Shared
  (* Uniqueness_mode.constrain_lower uniqueness *)

  let constrain_global_shared {locality; uniqueness = _} =
    Locality_mode.constrain_lower locality, Shared
  (* Uniqueness_mode.constrain_upper uniqueness *)

  let newvar () =
    { locality = Locality_mode.newvar ();
      uniqueness = Amode Shared }

  let newvar_below { locality; uniqueness = _ } =
    let l = Locality_mode.newvar_below locality in
    let u = Amode Shared, false in
    { locality = fst l; uniqueness = fst u }, snd l || snd u

  let newvar_above { locality; uniqueness = _ } =
    let l = Locality_mode.newvar_above locality in
    let u = Amode Shared, false in
    { locality = fst l; uniqueness = fst u }, snd l || snd u

  let check_const { locality; uniqueness } =
    match Locality_mode.check_const locality with
    | Some l -> begin match Uniqueness_mode.check_const uniqueness with
      | Some u -> Some (l, u)
      | None -> None
      end
    | None -> None

  let print ppf { locality; uniqueness } =
    Format.fprintf ppf
      "@[<2>%a, %a@]"
      Locality_mode.print locality
      Uniqueness_mode.print uniqueness

(*
  let pp_c ppf = function
    | Global -> Printf.fprintf ppf "0"
    | Local -> Printf.fprintf ppf "1"
  let pp_v ppf v =
    let i = v.mvid in
    (if i < 26 then Printf.fprintf ppf "%c" (Char.chr (Char.code 'a' + i))
    else Printf.fprintf ppf "v%d" i);
    Printf.fprintf ppf "[%a%a]" pp_c v.lower pp_c v.upper
*)
end

module Value_mode = struct

  (* Modes are ordered so that [unique] is a submode of [shared] *)
  type uniqueness = Types.uniqueness = Unique | Shared

  (* Modes are ordered so that [global] is a submode of [local] *)
  type locality =
    | Global
    | Regional
    | Local

  type const = locality * uniqueness

  let r_as_l : const -> Alloc_mode.const = function
    | Global, u -> Global, u
    | Regional, u -> Local, u
    | Local, u -> Local, u
  [@@warning "-unused-value-declaration"]

  let r_as_g : const -> Alloc_mode.const = function
    | Global, u -> Global, u
    | Regional, u -> Global, u
    | Local, u -> Local, u
  [@@warning "-unused-value-declaration"]

  let of_alloc_consts
        ~(r_as_l : Alloc_mode.locality)
        ~(r_as_g : Alloc_mode.locality) =
    match r_as_l, r_as_g with
    | Global, Global -> Global
    | Global, Local -> assert false
    | Local, Global -> Regional
    | Local, Local -> Local

  type t = Types.value_mode =
    { r_as_l : Alloc_mode.locality Types.mode;
      (* [r_as_l] is the image of the mode under the [r_as_l] function *)
      r_as_g : Alloc_mode.locality Types.mode;
      (* [r_as_g] is the image of the mode under the [r_as_g] function.
         Always less than [r_as_l]. *)
      uniqueness : uniqueness Types.mode }

  let global =
    let r_as_l = Locality_mode.global in
    let r_as_g = Locality_mode.global in
    { r_as_l; r_as_g; uniqueness = Amode Shared }

  let regional =
    let r_as_l = Locality_mode.local in
    let r_as_g = Locality_mode.global in
    { r_as_l; r_as_g ; uniqueness = Amode Shared }

  let local =
    let r_as_l = Locality_mode.local in
    let r_as_g = Locality_mode.local in
    { r_as_l; r_as_g; uniqueness = Amode Shared }

  let global_unique =
    let r_as_l = Locality_mode.global in
    let r_as_g = Locality_mode.global in
    { r_as_l; r_as_g; uniqueness = Amode Unique }

  let regional_unique =
    let r_as_l = Locality_mode.local in
    let r_as_g = Locality_mode.global in
    { r_as_l; r_as_g ; uniqueness = Amode Unique }

  let local_unique =
    let r_as_l = Locality_mode.local in
    let r_as_g = Locality_mode.local in
    { r_as_l; r_as_g; uniqueness = Amode Unique }

  let of_const = function
    | Global, Shared -> global
    | Regional, Shared -> regional
    | Local, Shared -> local
    | Global, Unique -> global_unique
    | Regional, Unique -> regional_unique
    | Local, Unique -> local_unique

  let max_mode =
    let r_as_l = Locality_mode.max_mode in
    let r_as_g = Locality_mode.max_mode in
    let uniqueness = Uniqueness_mode.max_mode in
    { r_as_l; r_as_g; uniqueness }

  let min_mode =
    let r_as_l = Locality_mode.min_mode in
    let r_as_g = Locality_mode.min_mode in
    let uniqueness = Uniqueness_mode.min_mode in
    { r_as_l; r_as_g; uniqueness }

  let of_alloc {locality ; uniqueness } =
    let r_as_l = locality in
    let r_as_g = locality in
    { r_as_l; r_as_g; uniqueness }

  let local_to_regional t = { t with r_as_g = Locality_mode.global }

  let regional_to_global t = { t with r_as_l = t.r_as_g }

  let regional_to_local t = { t with r_as_g = t.r_as_l }

  let global_to_regional t = { t with r_as_l = Locality_mode.local }

  let regional_to_global_alloc t = { locality = t.r_as_g; uniqueness = t.uniqueness }

  let regional_to_local_alloc t = { locality = t.r_as_l; uniqueness = t.uniqueness }

  type error = [`Regionality | `Locality | `Uniqueness]

  let submode t1 t2 =
    match Locality_mode.submode t1.r_as_l t2.r_as_l with
    | Error () -> Error `Regionality
    | Ok () -> begin
        match Locality_mode.submode t1.r_as_g t2.r_as_g with
        | Ok () -> begin match Uniqueness_mode.submode t1.uniqueness t2.uniqueness with
          | Ok () as ok -> ok
          | Error () -> Error `Uniqueness
        end
        | Error () -> Error `Locality
      end

  let submode_exn t1 t2 =
    match submode t1 t2 with
    | Ok () -> ()
    | Error _ -> invalid_arg "submode_exn"

  let rec submode_meet t = function
    | [] -> Ok ()
    | t' :: rest ->
      match submode t t' with
      | Ok () -> submode_meet t rest
      | Error _ as err -> err

  let join ts =
    let r_as_l = Locality_mode.join (List.map (fun t -> t.r_as_l) ts) in
    let r_as_g = Locality_mode.join (List.map (fun t -> t.r_as_g) ts) in
    let uniqueness = Amode Shared in
    { r_as_l; r_as_g; uniqueness }

  let constrain_upper t =
    let r_as_l = Locality_mode.constrain_upper t.r_as_l in
    let r_as_g = Locality_mode.constrain_upper t.r_as_g in
    let uniqueness = Shared in
    of_alloc_consts ~r_as_l ~r_as_g, uniqueness

  let constrain_lower t =
    let r_as_l = Locality_mode.constrain_lower t.r_as_l in
    let r_as_g = Locality_mode.constrain_lower t.r_as_g in
    let uniqueness = Shared in
    of_alloc_consts ~r_as_l ~r_as_g, uniqueness

  let newvar () =
    let r_as_l = Locality_mode.newvar () in
    let r_as_g = Locality_mode.newvar () in
    let uniqueness = Amode Shared in
    Locality_mode.submode_exn r_as_g r_as_l;
    { r_as_l; r_as_g; uniqueness }

  let check_const t =
    match Locality_mode.check_const t.r_as_l with
    | None -> None
    | Some r_as_l ->
      match Locality_mode.check_const t.r_as_g with
      | None -> None
      | Some r_as_g -> match Uniqueness_mode.check_const t.uniqueness with
        | None -> None
        | Some uniqueness ->
        Some (of_alloc_consts ~r_as_l ~r_as_g, uniqueness)

  let print_const ppf = function
    | Global, Shared -> Format.fprintf ppf "Global, Shared"
    | Regional, Shared -> Format.fprintf ppf "Regional, Shared"
    | Local, Shared -> Format.fprintf ppf "Local, Shared"
    | Global, Unique -> Format.fprintf ppf "Global, Unique"
    | Regional, Unique -> Format.fprintf ppf "Regional, Unique"
    | Local, Unique -> Format.fprintf ppf "Local, Unique"

  let print ppf t =
    match check_const t with
    | Some const -> print_const ppf const
    | None ->
        Format.fprintf ppf
          "@[<2>r_as_l: %a@ r_as_g: %a@ uniqueness: %a@]"
          Locality_mode.print t.r_as_l
          Locality_mode.print t.r_as_g
          Uniqueness_mode.print t.uniqueness

end
