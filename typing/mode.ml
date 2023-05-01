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
open Either
include Modes

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

module type DualLattice = sig
  module D : Lattice

  type const

  val to_dconst : const -> D.const
  val from_dconst : D.const -> const
  val print_const : Format.formatter -> const -> unit
end

(* The interface we provide to the user would build a directed graph where
   nodes are modes (either const or var) and edges are submoding relation.
   Solving constraints directly on this graph directly would of course be very
   inefficient. Instead, we use the following data structure which can be derived
   from the above virtual graph. First of all, for each var, we store all vars
   that are directly (not recursively) less or equal than it, called `vlower`. In
   additiona, we store the lower and upper bound for the variable, called `lower`
   and `upper`.

   To help understand, we also note the following:
   - If a const sit between two vars, there is no point to record the indirect relation
   between the two; instead, it's more straightward to record each of their
   relation to the const.
   - If a is in v.vlower, than a.lower <= v.lower and a.upper <= v.upper. We need
   to maintain this invariant.
   - `upper` and `lower` will not change unless some const is involved. If v.upper
   = v.lower, than v is determined.
*)
module Solver (L : Lattice) = struct
  type t = L.const mode

  exception NotSubmode

  let min_mode = Amode L.min_const
  let max_mode = Amode L.max_const
  let is_const = function Amode _ -> true | Amodevar _ -> false

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
    else
      let m = L.join_const v.lower m in
      set_lower ~log v m;
      if L.eq_const m v.upper then set_vlower ~log v []

  let rec submode_vc ~log v m =
    (* Printf.printf "  %a <= %a\n" pp_v v pp_c m; *)
    if L.le_const v.upper m then ()
    else if not (L.le_const v.lower m) then raise NotSubmode
    else
      let m = L.meet_const v.upper m in
      set_upper ~log v m;
      v.vlower
      |> List.iter (fun a ->
             (* a <= v <= m *)
             submode_vc ~log a m;
             (* The following is needed because a.lower might have been updated in
                submode_cv while v.lower is not, because from `a` we cannot find `v` *)
             (* In contrast, the `upper` field is always updated timely, because we
                have `vlower` *)
             set_lower ~log v (L.join_const v.lower a.lower));
      if L.eq_const v.lower m then set_vlower ~log v []

  let submode_vv ~log a b =
    (* Printf.printf "  %a <= %a\n" pp_v a pp_v b; *)
    if L.le_const a.upper b.lower then ()
    else if a == b || List.memq a b.vlower then ()
    else (
      (* the ordering of the following three clauses doesn't matter
         as they operate on different things *)
      submode_vc ~log a b.upper;
      set_vlower ~log b (a :: b.vlower);
      submode_cv ~log a.lower b
      (* as mentioned, at this point, vars larger than `b` will have
         `lower` out-of-date *))

  let submode a b =
    let log_head = ref Unchanged in
    let log = ref log_head in
    match
      match (a, b) with
      | Amode a, Amode b -> if not (L.le_const a b) then raise NotSubmode
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
    match (submode a b, submode b a) with
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
    {
      upper = L.max_const;
      lower = L.min_const;
      vlower = [];
      mvid = !next_id;
      mark = false;
    }

  let newvar () = Amodevar (fresh ())

  let newvar_below = function
    | Amode c when L.eq_const c L.min_const -> (min_mode, false)
    | m ->
        let v = newvar () in
        submode_exn v m;
        (v, true)

  let newvar_above = function
    | Amode c when L.eq_const c L.max_const -> (max_mode, false)
    | m ->
        let v = newvar () in
        submode_exn m v;
        (v, true)

  let rec all_equal v = function
    | [] -> true
    | v' :: rest -> if v == v' then all_equal v rest else false

  let joinvars vars =
    match vars with
    | [] -> min_mode
    | v :: rest ->
        let v =
          if all_equal v rest then v
          else
            let v = fresh () in
            List.iter (fun v' -> submode_exn (Amodevar v') (Amodevar v)) vars;
            v
        in
        Amodevar v

  let meetvars vars =
    match vars with
    | [] -> max_mode
    | v :: rest ->
        let v =
          if all_equal v rest then v
          else
            let v = fresh () in
            List.iter (fun v' -> submode_exn (Amodevar v) (Amodevar v')) vars;
            v
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
      else (
        mark v';
        new_vlower := v' :: !new_vlower;
        trans_low v')
    and trans_low v' =
      assert (v != v');
      if not (L.le_const v'.lower v.upper) then
        Misc.fatal_error "compress_vlower: invalid bounds";
      if not (L.le_const v'.lower !new_lower) then (
        new_lower := L.join_const !new_lower v'.lower;
        if !new_lower = v.upper then
          (* v is now a constant, no need to keep computing bounds *)
          raise Became_constant);
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
    if !new_lower != v.lower || !new_vlower != v.vlower then (
      let log_head = ref Unchanged in
      let log = ref log_head in
      set_lower ~log v !new_lower;
      set_vlower ~log v !new_vlower;
      log_changes !log_head !log)

  let constrain_lower = function
    | Amode m -> m
    | Amodevar v ->
        compress_vlower v;
        submode_exn (Amodevar v) (Amode v.lower);
        v.lower

  let check_const' = function
    | Amode m -> Either.Left m
    | Amodevar v ->
        compress_vlower v;
        if L.eq_const v.lower v.upper then Left v.lower else Right v

  let check_const a =
    match check_const' a with Left m -> Some m | Right _ -> None

  let print_var_id ppf v = Format.fprintf ppf "?%i" v.mvid

  let print_var ppf v =
    if v.vlower = [] then print_var_id ppf v
    else
      Format.fprintf ppf "%a[> %a]" print_var_id v
        (Format.pp_print_list print_var_id)
        v.vlower

  let print' ?(verbose = true) ?label ppf a =
    match check_const' a with
    | Left m -> L.print_const ppf m
    | Right v ->
        (match label with None -> () | Some s -> Format.fprintf ppf "%s:" s);
        if verbose then print_var ppf v else Format.fprintf ppf "?"

  let print ppf a = print' ~verbose:true ?label:None ppf a
end

module DualSolver (DL : DualLattice) = struct
  module S = Solver (DL.D)

  type t = DL.D.const dmode

  let is_const (Dualized a) = S.is_const a

  let join_const a b =
    DL.from_dconst (DL.D.meet_const (DL.to_dconst a) (DL.to_dconst b))

  let meet_const a b =
    DL.from_dconst (DL.D.join_const (DL.to_dconst a) (DL.to_dconst b))

  let le_const a b = DL.D.le_const (DL.to_dconst b) (DL.to_dconst a)
  let min_const = DL.from_dconst DL.D.max_const
  let max_const = DL.from_dconst DL.D.min_const
  let submode (Dualized a) (Dualized b) = S.submode b a
  let submode_exn (Dualized a) (Dualized b) = S.submode_exn b a
  let equate (Dualized a) (Dualized b) = S.equate b a
  let constrain_upper (Dualized a) = DL.from_dconst (S.constrain_lower a)
  let constrain_lower (Dualized a) = DL.from_dconst (S.constrain_upper a)
  let to_dual (Dualized a) = a
  let from_dual a = Dualized a
  let min_mode = from_dual S.max_mode
  let max_mode = from_dual S.min_mode
  let newvar () = Dualized (S.newvar ())

  let newvar_below (Dualized a) =
    let a', boo = S.newvar_above a in
    (Dualized a', boo)

  let newvar_above (Dualized a) =
    let a', boo = S.newvar_below a in
    (Dualized a', boo)

  let check_const (Dualized a) =
    match S.check_const a with
    | Some m -> Some (DL.from_dconst m)
    | None -> None

  let print' ?(verbose = true) ?label ppf (Dualized a) =
    match S.check_const' a with
    | Left m -> DL.print_const ppf (DL.from_dconst m)
    | Right v ->
        (match label with None -> () | Some s -> Format.fprintf ppf "%s:" s);
        if verbose then
          (* caret stands for dual *)
          Format.fprintf ppf "^%a" S.print_var v
        else Format.fprintf ppf "?"

  let print ppf m = print' ~verbose:true ?label:None ppf m
end

module Locality = struct
  module T = struct
    type const = Modes.Locality.const = Global | Local

    let min_const = Global
    let max_const = Local

    let le_const a b =
      match (a, b) with Global, _ | _, Local -> true | Local, Global -> false

    let eq_const a b =
      match (a, b) with
      | Global, Global | Local, Local -> true
      | Local, Global | Global, Local -> false

    let join_const a b =
      match (a, b) with
      | Local, _ | _, Local -> Local
      | Global, Global -> Global

    let meet_const a b =
      match (a, b) with
      | Global, _ | _, Global -> Global
      | Local, Local -> Local

    let print_const ppf = function
      | Global -> Format.fprintf ppf "Global"
      | Local -> Format.fprintf ppf "Local"
  end

  include T
  include Solver (T)

  let global = Amode Global
  let local = Amode Local
  let legacy = global
  let constrain_legacy = constrain_lower
  let of_const = function Global -> global | Local -> local

  let join ms =
    let rec aux vars = function
      | [] -> joinvars vars
      | Amode Global :: ms -> aux vars ms
      | Amode Local :: _ -> Amode Local
      | Amodevar v :: ms -> aux (v :: vars) ms
    in
    aux [] ms
end

module Uniqueness = struct
  module T = struct
    type const = Modes.Uniqueness.const = Unique | Shared

    let min_const = Unique
    let max_const = Shared

    let le_const a b =
      match (a, b) with
      | Unique, _ | _, Shared -> true
      | Shared, Unique -> false

    let eq_const a b =
      match (a, b) with
      | Unique, Unique | Shared, Shared -> true
      | Shared, Unique | Unique, Shared -> false

    let join_const a b =
      match (a, b) with
      | Shared, _ | _, Shared -> Shared
      | Unique, Unique -> Unique

    let meet_const a b =
      match (a, b) with
      | Unique, _ | _, Unique -> Unique
      | Shared, Shared -> Shared

    let print_const ppf = function
      | Shared -> Format.fprintf ppf "Shared"
      | Unique -> Format.fprintf ppf "Unique"
  end

  include T
  include Solver (T)

  let constrain_legacy = constrain_upper
  let unique = Amode Unique
  let shared = Amode Shared
  let legacy = shared
  let of_const = function Unique -> unique | Shared -> shared

  let join ms =
    let rec aux vars = function
      | [] -> joinvars vars
      | Amode Unique :: ms -> aux vars ms
      | Amode Shared :: _ -> Amode Shared
      | Amodevar v :: ms -> aux (v :: vars) ms
    in
    aux [] ms

  let meet ms =
    let rec aux vars = function
      | [] -> meetvars vars
      | Amode Unique :: _ -> Amode Unique
      | Amode Shared :: ms -> aux vars ms
      | Amodevar v :: ms -> aux (v :: vars) ms
    in
    aux [] ms
end

module Linearity = struct
  module DL = struct
    type const = Modes.Linearity.const = Many | Once

    module D = Uniqueness.T

    let print_const ppf = function
      | Once -> Format.fprintf ppf "Once"
      | Many -> Format.fprintf ppf "Many"

    let to_dconst = function Once -> D.Unique | Many -> D.Shared
    let from_dconst = function D.Unique -> Once | D.Shared -> Many
  end

  include DL
  include DualSolver (DL)

  let once = Dualized (Amode DL.D.Unique)
  let many = Dualized (Amode DL.D.Shared)
  let legacy = many
  let constrain_legacy = constrain_lower
  let of_const = function Many -> many | Once -> once

  let join ms =
    (* CR zqian: need more efficient impl *)
    let v = newvar () in
    List.iter (fun x -> submode_exn x v) ms;
    v
end

module Alloc = struct
  include Modes.Alloc

  let of_const { locality; uniqueness; linearity } : t =
    {
      locality = Locality.of_const locality;
      uniqueness = Uniqueness.of_const uniqueness;
      linearity = Linearity.of_const linearity;
    }

  let legacy =
    {
      locality = Locality.legacy;
      uniqueness = Uniqueness.legacy;
      linearity = Linearity.legacy;
    }

  let local = { legacy with locality = Locality.local }
  let unique = { legacy with uniqueness = Uniqueness.unique }
  let local_unique = { local with uniqueness = Uniqueness.unique }

  let is_const { locality; uniqueness; linearity } =
    Locality.is_const locality
    && Uniqueness.is_const uniqueness
    && Linearity.is_const linearity

  let min_mode : t =
    {
      locality = Locality.min_mode;
      uniqueness = Uniqueness.min_mode;
      linearity = Linearity.min_mode;
    }

  let max_mode : t =
    {
      locality = Locality.max_mode;
      uniqueness = Uniqueness.max_mode;
      linearity = Linearity.max_mode;
    }

  type error = [ `Locality | `Uniqueness | `Linearity ]

  let submode { locality = loc1; uniqueness = u1; linearity = lin1 }
      { locality = loc2; uniqueness = u2; linearity = lin2 } =
    match Locality.submode loc1 loc2 with
    | Ok () -> (
        match Uniqueness.submode u1 u2 with
        | Ok () -> (
            match Linearity.submode lin1 lin2 with
            | Ok () -> Ok ()
            | Error () -> Error `Linearity)
        | Error () -> Error `Uniqueness)
    | Error () -> Error `Locality

  let submode_exn ({ locality = loc1; uniqueness = u1; linearity = lin1 } : t)
      ({ locality = loc2; uniqueness = u2; linearity = lin2 } : t) =
    Locality.submode_exn loc1 loc2;
    Uniqueness.submode_exn u1 u2;
    Linearity.submode_exn lin1 lin2

  let equate ({ locality = loc1; uniqueness = u1; linearity = lin1 } : t)
      ({ locality = loc2; uniqueness = u2; linearity = lin2 } : t) =
    match Locality.equate loc1 loc2 with
    | Ok () -> (
        match Uniqueness.equate u1 u2 with
        | Ok () -> (
            match Linearity.equate lin1 lin2 with
            | Ok () -> Ok ()
            | Error () -> Error `Linearity)
        | Error () -> Error `Uniqueness)
    | Error () -> Error `Locality

  let join_const { locality = loc1; uniqueness = u1; linearity = lin1 }
      { locality = loc2; uniqueness = u2; linearity = lin2 } =
    {
      locality = Locality.join_const loc1 loc2;
      uniqueness = Uniqueness.join_const u1 u2;
      linearity = Linearity.join_const lin1 lin2;
    }

  let join ms : t =
    {
      locality = Locality.join (List.map (fun (t : t) -> t.locality) ms);
      uniqueness = Uniqueness.join (List.map (fun (t : t) -> t.uniqueness) ms);
      linearity = Linearity.join (List.map (fun (t : t) -> t.linearity) ms);
    }

  let constrain_upper { locality; uniqueness; linearity } =
    {
      locality = Locality.constrain_upper locality;
      uniqueness = Uniqueness.constrain_upper uniqueness;
      linearity = Linearity.constrain_upper linearity;
    }

  let constrain_lower { locality; uniqueness; linearity } =
    {
      locality = Locality.constrain_lower locality;
      uniqueness = Uniqueness.constrain_lower uniqueness;
      linearity = Linearity.constrain_lower linearity;
    }

  (* constrain to the legacy modes*)
  let constrain_legacy { locality; uniqueness; linearity } =
    {
      locality = Locality.constrain_legacy locality;
      uniqueness = Uniqueness.constrain_legacy uniqueness;
      linearity = Linearity.constrain_legacy linearity;
    }

  let newvar () =
    {
      locality = Locality.newvar ();
      uniqueness = Uniqueness.newvar ();
      linearity = Linearity.newvar ();
    }

  let newvar_below { locality; uniqueness; linearity } =
    let locality, changed1 = Locality.newvar_below locality in
    let uniqueness, changed2 = Uniqueness.newvar_below uniqueness in
    let linearity, changed3 = Linearity.newvar_below linearity in
    ({ locality; uniqueness; linearity }, changed1 || changed2 || changed3)

  let newvar_above { locality; uniqueness; linearity } =
    let locality, changed1 = Locality.newvar_above locality in
    let uniqueness, changed2 = Uniqueness.newvar_above uniqueness in
    let linearity, changed3 = Linearity.newvar_above linearity in
    ({ locality; uniqueness; linearity }, changed1 || changed2 || changed3)

  let of_uniqueness uniqueness =
    {
      locality = Locality.newvar ();
      uniqueness;
      linearity = Linearity.newvar ();
    }

  let of_locality locality =
    {
      locality;
      uniqueness = Uniqueness.newvar ();
      linearity = Linearity.newvar ();
    }

  let of_linearity linearity =
    {
      locality = Locality.newvar ();
      uniqueness = Uniqueness.newvar ();
      linearity;
    }

  let with_locality locality t = { t with locality }
  let with_uniqueness uniqueness t = { t with uniqueness }
  let with_linearity linearity t = { t with linearity }

  let check_const { locality; uniqueness; linearity } =
    {
      locality = Locality.check_const locality;
      uniqueness = Uniqueness.check_const uniqueness;
      linearity = Linearity.check_const linearity;
    }

  let print' ?(verbose = true) ppf { locality; uniqueness; linearity } =
    Format.fprintf ppf "%a, %a, %a"
      (Locality.print' ~verbose ~label:"locality")
      locality
      (Uniqueness.print' ~verbose ~label:"uniqueness")
      uniqueness
      (Linearity.print' ~verbose ~label:"linearity")
      linearity

  let print ppf m = print' ~verbose:true ppf m
end

module Regionality = struct
  include Modes.Regionality

  let r_as_l : const -> Locality.const = function
    | Local -> Local
    | Regional -> Local
    | Global -> Global

  let r_as_g : const -> Locality.const = function
    | Local -> Local
    | Regional -> Global
    | Global -> Global

  let const_of_locality ~(r_as_l : Locality.const) ~(r_as_g : Locality.const) =
    match (r_as_l, r_as_g) with
    | Global, Global -> Global
    | Global, Local -> assert false
    | Local, Global -> Regional
    | Local, Local -> Local

  let of_locality l = { r_as_l = l; r_as_g = l }

  let of_const c =
    let r_as_l, r_as_g =
      match c with
      | Global -> (Locality.global, Locality.global)
      | Regional -> (Locality.local, Locality.global)
      | Local -> (Locality.local, Locality.local)
    in
    { r_as_l; r_as_g }

  let local = of_const Local
  let regional = of_const Regional
  let global = of_const Global
  let legacy = global

  let max_mode =
    let r_as_l = Locality.max_mode in
    let r_as_g = Locality.max_mode in
    { r_as_l; r_as_g }

  let min_mode =
    let r_as_l = Locality.min_mode in
    let r_as_g = Locality.min_mode in
    { r_as_l; r_as_g }

  let local_to_regional t = { t with r_as_g = Locality.global }
  let regional_to_global t = { t with r_as_l = t.r_as_g }
  let regional_to_local t = { t with r_as_g = t.r_as_l }
  let regional_to_global_locality t = t.r_as_g
  let regional_to_local_locality t = t.r_as_l
  let global_to_regional t = { t with r_as_l = Locality.local }

  type error = [ `Regionality | `Locality ]

  let submode t1 t2 =
    match Locality.submode t1.r_as_l t2.r_as_l with
    | Error () -> Error `Regionality
    | Ok () -> (
        match Locality.submode t1.r_as_g t2.r_as_g with
        | Error () -> Error `Locality
        | Ok () as ok -> ok)

  let equate a b =
    match (submode a b, submode b a) with
    | Ok (), Ok () -> Ok ()
    | Error e, _ | _, Error e -> Error e

  let join ts =
    let r_as_l = Locality.join (List.map (fun t -> t.r_as_l) ts) in
    let r_as_g = Locality.join (List.map (fun t -> t.r_as_g) ts) in
    { r_as_l; r_as_g }

  let constrain_upper t =
    let r_as_l = Locality.constrain_upper t.r_as_l in
    let r_as_g = Locality.constrain_upper t.r_as_g in
    const_of_locality ~r_as_l ~r_as_g

  let constrain_lower t =
    let r_as_l = Locality.constrain_lower t.r_as_l in
    let r_as_g = Locality.constrain_lower t.r_as_g in
    const_of_locality ~r_as_l ~r_as_g

  let newvar () =
    let r_as_l = Locality.newvar () in
    let r_as_g, _ = Locality.newvar_below r_as_l in
    { r_as_l; r_as_g }

  let newvar_below t =
    let r_as_l, changed1 = Locality.newvar_below t.r_as_l in
    let r_as_g, changed2 = Locality.newvar_below t.r_as_g in
    Locality.submode_exn r_as_g r_as_l;
    ({ r_as_l; r_as_g }, changed1 || changed2)

  let newvar_above t =
    let r_as_l, changed1 = Locality.newvar_above t.r_as_l in
    let r_as_g, changed2 = Locality.newvar_above t.r_as_g in
    Locality.submode_exn r_as_g r_as_l;
    ({ r_as_l; r_as_g }, changed1 || changed2)

  let check_const t =
    match Locality.check_const t.r_as_l with
    | None -> None
    | Some r_as_l -> (
        match Locality.check_const t.r_as_g with
        | None -> None
        | Some r_as_g -> Some (const_of_locality ~r_as_l ~r_as_g))

  let print_const ppf t =
    let s =
      match t with
      | Global -> "Global"
      | Regional -> "Regional"
      | Local -> "Local"
    in
    Format.fprintf ppf "%s" s

  let print' ?(verbose = true) ?label ppf t =
    match check_const t with
    | Some l -> print_const ppf l
    | None -> (
        match label with
        | None -> ()
        | Some l ->
            Format.fprintf ppf "%s: " l;
            Format.fprintf ppf "r_as_l=%a r_as_g=%a"
              (Locality.print' ~verbose ?label:None)
              t.r_as_l
              (Locality.print' ~verbose ?label:None)
              t.r_as_g)

  let print ppf m = print' ~verbose:true ?label:None ppf m
end

module Value = struct
  include Modes.Value

  let r_as_l : const -> Alloc.const = function
    | { locality; uniqueness; linearity } ->
        { locality = Regionality.r_as_l locality; uniqueness; linearity }
    [@@warning "-unused-value-declaration"]

  let r_as_g : const -> Alloc.const = function
    | { locality; uniqueness; linearity } ->
        { locality = Regionality.r_as_g locality; uniqueness; linearity }
    [@@warning "-unused-value-declaration"]

  let legacy =
    {
      locality = Regionality.legacy;
      uniqueness = Uniqueness.legacy;
      linearity = Linearity.legacy;
    }

  let regional = { legacy with locality = Regionality.regional }
  let local = { legacy with locality = Regionality.local }
  let unique = { legacy with uniqueness = Uniqueness.unique }
  let regional_unique = { regional with uniqueness = Uniqueness.unique }
  let local_unique = { local with uniqueness = Uniqueness.unique }

  let of_const { locality; uniqueness; linearity } =
    {
      locality = Regionality.of_const locality;
      uniqueness = Uniqueness.of_const uniqueness;
      linearity = Linearity.of_const linearity;
    }

  let max_mode =
    let locality = Regionality.max_mode in
    let uniqueness = Uniqueness.max_mode in
    let linearity = Linearity.max_mode in
    { locality; uniqueness; linearity }

  let min_mode =
    let locality = Regionality.min_mode in
    let uniqueness = Uniqueness.min_mode in
    let linearity = Linearity.min_mode in
    { locality; uniqueness; linearity }

  let min_with_uniqueness u = { min_mode with uniqueness = u }
  let max_with_uniqueness u = { max_mode with uniqueness = u }

  let min_with_locality l =
    { min_mode with locality = Regionality.of_locality l }

  let max_with_locality l =
    { max_mode with locality = Regionality.of_locality l }

  let with_locality locality t = { t with locality }
  let with_uniqueness uniqueness t = { t with uniqueness }
  let with_linearity linearity t = { t with linearity }
  let to_local t = { t with locality = Regionality.local }
  let to_global t = { t with locality = Regionality.global }
  let to_unique t = { t with uniqueness = Uniqueness.unique }
  let to_once t = { t with linearity = Linearity.once }
  let to_shared t = { t with uniqueness = Uniqueness.shared }

  let of_alloc { locality; uniqueness; linearity } =
    let locality = Regionality.of_locality locality in
    { locality; uniqueness; linearity }

  let local_to_regional t =
    { t with locality = Regionality.local_to_regional t.locality }

  let regional_to_global t =
    { t with locality = Regionality.regional_to_global t.locality }

  let regional_to_local t =
    { t with locality = Regionality.regional_to_local t.locality }

  let global_to_regional t =
    { t with locality = Regionality.global_to_regional t.locality }

  let regional_to_global_alloc t =
    { t with locality = Regionality.regional_to_global_locality t.locality }

  let regional_to_local_alloc t =
    { t with locality = Regionality.regional_to_local_locality t.locality }

  let regional_to_global_locality t =
    Regionality.regional_to_global_locality t.locality

  let regional_to_local_locality t =
    Regionality.regional_to_local_locality t.locality

  type error = [ `Regionality | `Locality | `Uniqueness | `Linearity ]

  let submode t1 t2 =
    match Regionality.submode t1.locality t2.locality with
    | Error _ as e -> e
    | Ok () -> (
        match Uniqueness.submode t1.uniqueness t2.uniqueness with
        | Error () -> Error `Uniqueness
        | Ok () -> (
            match Linearity.submode t1.linearity t2.linearity with
            | Error () -> Error `Linearity
            | Ok () as ok -> ok))

  let submode_exn t1 t2 =
    match submode t1 t2 with
    | Ok () -> ()
    | Error _ -> invalid_arg "submode_exn"

  let equate ({ locality = loc1; uniqueness = u1; linearity = lin1 } : t)
      ({ locality = loc2; uniqueness = u2; linearity = lin2 } : t) =
    match Regionality.equate loc1 loc2 with
    | Ok () -> (
        match Uniqueness.equate u1 u2 with
        | Ok () -> (
            match Linearity.equate lin1 lin2 with
            | Ok () -> Ok ()
            | Error () -> Error `Linearity)
        | Error () -> Error `Uniqueness)
    | Error e -> Error e

  let rec submode_meet t = function
    | [] -> Ok ()
    | t' :: rest -> (
        match submode t t' with
        | Ok () -> submode_meet t rest
        | Error _ as err -> err)

  let join ts =
    let locality = Regionality.join (List.map (fun t -> t.locality) ts) in
    let uniqueness = Uniqueness.join (List.map (fun t -> t.uniqueness) ts) in
    let linearity = Linearity.join (List.map (fun t -> t.linearity) ts) in
    { locality; uniqueness; linearity }

  let constrain_upper t =
    let locality = Regionality.constrain_upper t.locality in
    let uniqueness = Uniqueness.constrain_upper t.uniqueness in
    let linearity = Linearity.constrain_upper t.linearity in
    { locality; uniqueness; linearity }

  let constrain_lower t =
    let locality = Regionality.constrain_lower t.locality in
    let uniqueness = Uniqueness.constrain_lower t.uniqueness in
    let linearity = Linearity.constrain_lower t.linearity in
    { locality; uniqueness; linearity }

  let newvar () =
    let locality = Regionality.newvar () in
    let uniqueness = Uniqueness.newvar () in
    let linearity = Linearity.newvar () in
    { locality; uniqueness; linearity }

  let newvar_below { locality; uniqueness; linearity } =
    let locality, changed1 = Regionality.newvar_below locality in
    let uniqueness, changed2 = Uniqueness.newvar_below uniqueness in
    let linearity, changed3 = Linearity.newvar_below linearity in
    ({ locality; uniqueness; linearity }, changed1 || changed2 || changed3)

  let newvar_above { locality; uniqueness; linearity } =
    let locality, changed1 = Regionality.newvar_above locality in
    let uniqueness, changed2 = Uniqueness.newvar_above uniqueness in
    let linearity, changed3 = Linearity.newvar_above linearity in
    ({ locality; uniqueness; linearity }, changed1 || changed2 || changed3)

  let check_const t =
    let locality = Regionality.check_const t.locality in
    let uniqueness = Uniqueness.check_const t.uniqueness in
    let linearity = Linearity.check_const t.linearity in
    { locality; uniqueness; linearity }

  let print' ?(verbose = true) ppf t =
    Format.fprintf ppf "%a, %a, %a"
      (Regionality.print' ~verbose ~label:"locality")
      t.locality
      (Uniqueness.print' ~verbose ~label:"uniqueness")
      t.uniqueness
      (Linearity.print' ~verbose ~label:"linearity")
      t.linearity

  let print ppf t = print' ~verbose:true ppf t
end
