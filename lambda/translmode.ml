open Lambda

let transl_locality_mode locality =
  match Mode.Locality.constrain_lower locality with
  | Global -> alloc_heap
  | Local -> alloc_local

let transl_alloc_mode {Mode.locality; _} =
(* we only take the locality axis *)
  transl_locality_mode locality

let transl_modify_mode locality =
  match Mode.Locality.constrain_lower locality with
  | Global -> modify_heap
  | Local -> modify_maybe_stack