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

open Types
open Btype

module type Lattice = sig
  type const
  val min_const : const
  val max_const : const
  val eq_const : const -> const -> bool
  val le_const : const -> const -> bool
  val join_const : const -> const -> const
  val meet_const : const -> const -> const
  val print_const : Format.formatter -> const -> unit
end

module Solver (L : Lattice) = struct
  exception NotSubmode

  let min_mode = Amode L.min_const
  let max_mode = Amode L.max_const

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
      if L.eq_const m v.upper then set_vlower ~log v []
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
      if L.eq_const v.lower m then set_vlower ~log v []
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

  let newvar () = Amodevar (fresh ())

  let newvar_below = function
    | Amode c when L.eq_const c L.min_const -> Amode L.min_const, false
    | m ->
        let v = newvar () in
        submode_exn v m;
        v, true

  let newvar_above = function
    | Amode c when L.eq_const c L.max_const -> Amode L.max_const, false
    | m ->
        let v = newvar () in
        submode_exn m v;
        v, true

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
      if L.eq_const v.lower v.upper then Some v.lower else None

  let print_var_id ppf v =
    Format.fprintf ppf "?%i" v.mvid

  let print_var ppf v =
    compress_vlower v;
    if L.eq_const v.lower v.upper then begin
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

module Locality = struct
  module T = struct
    type const = Types.locality = Global | Local

    let min_const = Global
    let max_const = Local

    let le_const a b =
      match a, b with
      | Global, _ | _, Local -> true
      | Local, Global -> false

    let eq_const a b =
      match a, b with
      | Global, Global | Local, Local -> true
      | Local, Global | Global, Local -> false

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
  include Solver(T)

  type t = Types.locality Types.mode

  let global = Amode Global
  let local = Amode Local

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
end

module Uniqueness = struct
  module T = struct
    type const = Types.uniqueness = Unique | Shared

    let min_const = Unique
    let max_const = Shared

    let le_const a b =
      match a, b with
      | Unique, _ | _, Shared -> true
      | Shared, Unique -> false

    let eq_const a b =
      match a, b with
      | Unique, Unique | Shared, Shared -> true
      | Shared, Unique | Unique, Shared -> false

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
  include Solver(T)

  type t = Types.uniqueness Types.mode

  let unique = Amode Unique
  let shared = Amode Shared

  let of_const = function
    | Unique -> unique
    | Shared -> shared

  let join ms =
    let rec aux vars = function
      | [] -> joinvars vars
      | Amode Unique :: ms -> aux vars ms
      | Amode Shared :: _ -> Amode Shared
      | Amodevar v :: ms -> aux (v :: vars) ms
    in aux [] ms
end

module Alloc = struct
  (* Modes are ordered so that [global] is a submode of [local] *)
  type locality = Types.locality = Global | Local
  (* Modes are ordered so that [unique] is a submode of [shared] *)
  type uniqueness = Types.uniqueness = Unique | Shared
  type const = locality * uniqueness
  type t = Types.alloc_mode

  let of_const (l, u) = { locality = Locality.of_const l; uniqueness = Uniqueness.of_const u }

  let global = { locality = Locality.global; uniqueness = Uniqueness.shared }
  let local = { locality = Locality.local; uniqueness = Uniqueness.shared }
  let unique = { locality = Locality.global; uniqueness = Uniqueness.unique }
  let local_unique = { locality = Locality.local; uniqueness = Uniqueness.unique }

  let min_mode = unique
  let max_mode = local

  type error = [`Locality | `Uniqueness]

  let submode {locality = l1; uniqueness = u1} {locality = l2; uniqueness = u2} =
    match Locality.submode l1 l2 with
      | Ok () -> begin match Uniqueness.submode u1 u2 with
        | Ok () -> Ok ()
        | Error () -> Error `Uniqueness
        end
      | Error () -> Error `Locality

  let submode_exn {locality = l1; uniqueness = u1} {locality = l2; uniqueness = u2} =
    Locality.submode_exn l1 l2;
    Uniqueness.submode_exn u1 u2

  let equate {locality = l1; uniqueness = u1} {locality = l2; uniqueness = u2} =
    match Locality.equate l1 l2 with
    | Ok () -> begin match Uniqueness.equate u1 u2 with
      | Ok () -> Ok ()
      | Error () -> Error `Uniqueness
    end
    | Error () -> Error `Locality

  let join_const (l1, u1) (l2, u2) =
    (Locality.join_const l1 l2, Uniqueness.join_const u1 u2)

  let join ms =
    { locality = Locality.join (List.map (fun t -> t.locality) ms);
      uniqueness = Uniqueness.join (List.map (fun (t : t) -> t.uniqueness) ms) }

  let constrain_upper {locality; uniqueness} =
    Locality.constrain_upper locality,
    Uniqueness.constrain_upper uniqueness

  let constrain_lower {locality; uniqueness} =
    Locality.constrain_lower locality,
    Uniqueness.constrain_lower uniqueness

  let constrain_global_shared {locality; uniqueness} =
    Locality.constrain_lower locality,
    Uniqueness.constrain_upper uniqueness

  let newvar () =
    { locality = Locality.newvar ();
      uniqueness = Uniqueness.newvar () }

  let newvar_below { locality; uniqueness } =
    let l = Locality.newvar_below locality in
    let u = Uniqueness.newvar_below uniqueness in
    { locality = fst l; uniqueness = fst u }, snd l || snd u

  let newvar_above { locality; uniqueness } =
    let l = Locality.newvar_above locality in
    let u = Uniqueness.newvar_above uniqueness in
    { locality = fst l; uniqueness = fst u }, snd l || snd u

  let check_const { locality; uniqueness } =
    Locality.check_const locality, Uniqueness.check_const uniqueness

  let print ppf { locality; uniqueness } =
    Format.fprintf ppf
      "@[<2>%a, %a@]"
      Locality.print locality
      Uniqueness.print uniqueness

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

module Value = struct

  (* Modes are ordered so that [unique] is a submode of [shared] *)
  type uniqueness = Types.uniqueness = Unique | Shared

  (* Modes are ordered so that [global] is a submode of [local] *)
  type locality =
    | Global
    | Regional
    | Local

  type const = locality * uniqueness

  let r_as_l : const -> Alloc.const = function
    | Global, u -> Global, u
    | Regional, u -> Local, u
    | Local, u -> Local, u
  [@@warning "-unused-value-declaration"]

  let r_as_g : const -> Alloc.const = function
    | Global, u -> Global, u
    | Regional, u -> Global, u
    | Local, u -> Local, u
  [@@warning "-unused-value-declaration"]

  let of_alloc_consts
        ~(r_as_l : Alloc.locality)
        ~(r_as_g : Alloc.locality) =
    match r_as_l, r_as_g with
    | Global, Global -> Global
    | Global, Local -> assert false
    | Local, Global -> Regional
    | Local, Local -> Local

  type t = Types.value_mode =
    { r_as_l : Alloc.locality Types.mode;
      (* [r_as_l] is the image of the mode under the [r_as_l] function *)
      r_as_g : Alloc.locality Types.mode;
      (* [r_as_g] is the image of the mode under the [r_as_g] function.
         Always less than [r_as_l]. *)
      uniqueness : uniqueness Types.mode }

  let global =
    let r_as_l = Locality.global in
    let r_as_g = Locality.global in
    let uniqueness = Uniqueness.shared in
    { r_as_l; r_as_g; uniqueness }

  let regional =
    let r_as_l = Locality.local in
    let r_as_g = Locality.global in
    let uniqueness = Uniqueness.shared in
    { r_as_l; r_as_g ; uniqueness }

  let local =
    let r_as_l = Locality.local in
    let r_as_g = Locality.local in
    let uniqueness = Uniqueness.shared in
    { r_as_l; r_as_g; uniqueness }

  let global_unique =
    let r_as_l = Locality.global in
    let r_as_g = Locality.global in
    let uniqueness = Uniqueness.unique in
    { r_as_l; r_as_g; uniqueness }

  let regional_unique =
    let r_as_l = Locality.local in
    let r_as_g = Locality.global in
    let uniqueness = Uniqueness.unique in
    { r_as_l; r_as_g ; uniqueness }

  let local_unique =
    let r_as_l = Locality.local in
    let r_as_g = Locality.local in
    let uniqueness = Uniqueness.unique in
    { r_as_l; r_as_g; uniqueness }

  let of_const = function
    | Global, Shared -> global
    | Regional, Shared -> regional
    | Local, Shared -> local
    | Global, Unique -> global_unique
    | Regional, Unique -> regional_unique
    | Local, Unique -> local_unique

  let max_mode =
    let r_as_l = Locality.max_mode in
    let r_as_g = Locality.max_mode in
    let uniqueness = Uniqueness.max_mode in
    { r_as_l; r_as_g; uniqueness }

  let min_mode =
    let r_as_l = Locality.min_mode in
    let r_as_g = Locality.min_mode in
    let uniqueness = Uniqueness.min_mode in
    { r_as_l; r_as_g; uniqueness }

  let of_uniqueness_min u =
    { min_mode with uniqueness = u }

  let of_uniqueness_max u =
    { max_mode with uniqueness = u }

  let of_locality_min l =
    { min_mode with r_as_l = l; r_as_g = l }

  let of_locality_max l =
    { max_mode with r_as_l = l; r_as_g = l }

  let to_local t = { t with r_as_l = Locality.local; r_as_g = Locality.local }
  let to_global t = { t with r_as_l = Locality.global; r_as_g = Locality.global }
  let to_unique t = { t with uniqueness = Uniqueness.unique }
  let to_shared t = { t with uniqueness = Uniqueness.shared }

  let of_alloc {locality ; uniqueness } =
    let r_as_l = locality in
    let r_as_g = locality in
    { r_as_l; r_as_g; uniqueness }

  let local_to_regional t = { t with r_as_g = Locality.global }

  let regional_to_global t = { t with r_as_l = t.r_as_g }

  let regional_to_local t = { t with r_as_g = t.r_as_l }

  let global_to_regional t = { t with r_as_l = Locality.local }

  let regional_to_global_alloc t = { locality = t.r_as_g; uniqueness = t.uniqueness }

  let regional_to_local_alloc t = { locality = t.r_as_l; uniqueness = t.uniqueness }

  let regional_to_global_locality t = t.r_as_g

  let regional_to_local_locality t = t.r_as_l

  type error = [`Regionality | `Locality | `Uniqueness]

  let submode t1 t2 =
    match Locality.submode t1.r_as_l t2.r_as_l with
    | Error () -> Error `Regionality
    | Ok () -> begin
        match Locality.submode t1.r_as_g t2.r_as_g with
        | Ok () -> begin
          match Uniqueness.submode t1.uniqueness t2.uniqueness with
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
    let r_as_l = Locality.join (List.map (fun t -> t.r_as_l) ts) in
    let r_as_g = Locality.join (List.map (fun t -> t.r_as_g) ts) in
    let uniqueness = Uniqueness.join (List.map (fun t -> t.uniqueness) ts) in
    { r_as_l; r_as_g; uniqueness }

  let constrain_upper t =
    let r_as_l = Locality.constrain_upper t.r_as_l in
    let r_as_g = Locality.constrain_upper t.r_as_g in
    let uniqueness = Uniqueness.constrain_upper t.uniqueness in
    of_alloc_consts ~r_as_l ~r_as_g, uniqueness

  let constrain_lower t =
    let r_as_l = Locality.constrain_lower t.r_as_l in
    let r_as_g = Locality.constrain_lower t.r_as_g in
    let uniqueness = Uniqueness.constrain_lower t.uniqueness in
    of_alloc_consts ~r_as_l ~r_as_g, uniqueness

  let newvar () =
    let r_as_l = Locality.newvar () in
    let r_as_g, _ = Locality.newvar_below r_as_l in
    let uniqueness = Uniqueness.newvar () in
    { r_as_l; r_as_g; uniqueness }

  let newvar_below { r_as_l; r_as_g; uniqueness } =
    let r_as_l, b1 = Locality.newvar_below r_as_l in
    let r_as_g, b2 = Locality.newvar_below r_as_g in
    let uniqueness, b3 = Uniqueness.newvar_below uniqueness in
    Locality.submode_exn r_as_g r_as_l;
    { r_as_l; r_as_g; uniqueness }, b1 || b2 || b3

  let newvar_above { r_as_l; r_as_g; uniqueness } =
    let r_as_l, b1 = Locality.newvar_above r_as_l in
    let r_as_g, b2 = Locality.newvar_above r_as_g in
    let uniqueness, b3 = Uniqueness.newvar_above uniqueness in
    Locality.submode_exn r_as_g r_as_l;
    { r_as_l; r_as_g; uniqueness }, b1 || b2 || b3

  let check_const t =
    let locality = match Locality.check_const t.r_as_l with
    | None -> None
    | Some r_as_l ->
      match Locality.check_const t.r_as_g with
      | None -> None
      | Some r_as_g -> Some (of_alloc_consts ~r_as_l ~r_as_g) in
    let uniqueness = Uniqueness.check_const t.uniqueness in
    locality, uniqueness

  let print_const ppf (l, u) =
    let l = match l with
        | Global -> "Global"
        | Regional -> "Regional"
        | Local -> "Local" in
    let u = match u with
        | Unique -> "Unique"
        | Shared -> "Shared" in
    Format.fprintf ppf "%s %s" l u

  let print ppf t =
    match check_const t with
    | Some l, Some u ->
        print_const ppf (l, u);
    | _, _ ->
        Format.fprintf ppf
          "@[<2>r_as_l: %a@ r_as_g: %a@ uniqueness: %a@]"
          Locality.print t.r_as_l
          Locality.print t.r_as_g
          Uniqueness.print t.uniqueness

end
