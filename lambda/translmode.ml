open Lambda

let transl_locality_mode locality =
  match Mode.Locality.constrain_lower locality with
  | Global -> alloc_heap
  | Local -> alloc_local

let transl_uniqueness_mode uniqueness =
  match Mode.Uniqueness.constrain_lower uniqueness with
  | Unique -> alloc_unique
  | Shared -> alloc_shared

let transl_alloc_mode {Mode.locality; Mode.uniqueness; _} =
  ( transl_locality_mode locality
  , transl_uniqueness_mode uniqueness
  )

let transl_modify_mode alloc_mode =
  match Mode.Locality.constrain_lower alloc_mode with
  | Global -> modify_heap
  | Local -> modify_maybe_stack