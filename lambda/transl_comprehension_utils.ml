open Lambda

module Let_binding = struct
  type t =
    { let_kind   : let_kind
    ; value_kind : value_kind
    ; id         : Ident.t
    ; init       : lambda }

  let make_id let_kind value_kind name init =
    let id = Ident.create_local name in
    id, {let_kind; value_kind; id; init}

  let make_id' let_kind value_kind name init =
    snd @@ make_id let_kind value_kind name init

  let make_id_var let_kind value_kind name init =
    let id, binding = make_id let_kind value_kind name init in
    id, Lvar id, binding

  let make_var let_kind value_kind name init =
    let _id, var, binding = make_id_var let_kind value_kind name init in
    var, binding

  let let_one {let_kind; value_kind; id; init} body =
    Llet(let_kind, value_kind, id, init, body)

  let let_all = List.fold_right let_one
end

module Lambda_utils = struct
  module Make = struct
    let int n = Lconst (const_int n)

    let float f = Lconst (Const_base (Const_float (Float.to_string f)))

    let string ~loc s = Lconst (Const_base (Const_string(s, loc, None)))
  end

  let apply
        ?(tailcall    = Default_tailcall)
        ?(inlined     = Default_inlined)
        ?(specialised = Default_specialise)
        ?probe
        ~loc
        func
        args =
    Lapply { ap_loc         = loc
           ; ap_func        = func
           ; ap_args        = args
           ; ap_tailcall    = tailcall
           ; ap_inlined     = inlined
           ; ap_specialised = specialised
           ; ap_probe       = probe
           }

  module type Int_ops = sig
    (* We want to expose all the operators so we don't have to think about which
       ones to add and remove as we change the rest of the file *)

    val ( + ) : lambda -> lambda -> lambda
    val ( - ) : lambda -> lambda -> lambda
    val ( * ) : lambda -> lambda -> lambda
    val ( / ) : lambda -> lambda -> lambda

    val ( = )  : lambda -> lambda -> lambda
    val ( <> ) : lambda -> lambda -> lambda
    val ( < )  : lambda -> lambda -> lambda
    val ( > )  : lambda -> lambda -> lambda
    val ( <= ) : lambda -> lambda -> lambda
    val ( >= ) : lambda -> lambda -> lambda

    val ( && ) : lambda -> lambda -> lambda
    val ( || ) : lambda -> lambda -> lambda

    val l0 : lambda
    val l1 : lambda
    val i  : int -> lambda
  end

  let int_ops ~loc : (module Int_ops) = (module struct
    let binop prim l r = Lprim(prim, [l; r], loc)

    let ( + )  = binop Paddint
    let ( - )  = binop Psubint
    let ( * )  = binop Pmulint
    let ( / )  = binop (Pdivint Unsafe)
    let ( = )  = binop (Pintcomp Ceq)
    let ( <> ) = binop (Pintcomp Cne)
    let ( < )  = binop (Pintcomp Clt)
    let ( > )  = binop (Pintcomp Cgt)
    let ( <= ) = binop (Pintcomp Cle)
    let ( >= ) = binop (Pintcomp Cge)
    let ( && ) = binop Psequor
    let ( || ) = binop Psequor

    let i n = Lconst (const_int n)
    let l0 = i 0
    let l1 = i 1
  end)

  module Primitive = struct
    (** The Lambda primitive for calling a simple C primitive *)
    let c_prim name arity = Pccall (Primitive.simple ~name ~arity ~alloc:true)

    (** Create a function that produces the Lambda representation for a
        one-argument C primitive when provided with a Lambda argument *)
    let unary name =
      let prim = c_prim name 1 in
      fun ~loc x -> Lprim(prim, [x], loc)

    (** Create a function that produces the Lambda representation for a
        two-argument C primitive when provided with two Lambda arguments *)
    let binary name =
      let prim = c_prim name 2 in
      fun ~loc x y -> Lprim(prim, [x; y], loc)

    (** Create a function that produces the Lambda representation for a
        three-argument C primitive when provided with three Lambda arguments *)
    let ternary name =
      let prim = c_prim name 3 in
      fun ~loc x y z -> Lprim(prim, [x; y; z], loc)

    (* CR aspectorzabusky: These primitives are now created unconditionally on
       compiler startup.  Is that okay? *)

    let make_vect =
      let make_vect = binary "caml_make_vect" in
      fun ~loc ~length ~init -> make_vect ~loc length init

    let make_float_vect = unary "caml_make_float_vect"

    let array_append = binary "caml_array_append"

    let array_sub =
      let array_sub = ternary "caml_array_sub" in
      fun ~loc a ~offset ~length -> array_sub ~loc a offset length
  end
end

module Cps_utils = struct
  (** Function composition *)
  let compose f g x = f (g x)

  (** Apply a function to the first part of a tuple *)
  let first f (x, y) = f x, y

  let compose_map f =
    List.fold_left (fun k -> compose (compose k) f) Fun.id

  let compose_map_acc f =
    List.fold_left_map (fun k -> compose (first (compose k)) f) Fun.id
end
