val transl_locality_mode_l : (Mode.allowed * 'r) Mode.Locality.t -> Lambda.locality_mode

val transl_alloc_mode_l : (Mode.allowed * 'r) Mode.Alloc.t -> Lambda.alloc_mode
val transl_alloc_mode_r : ('l * Mode.allowed) Mode.Alloc.t -> Lambda.alloc_mode

val transl_modify_mode : (Mode.allowed * 'r) Mode.Locality.t -> Lambda.modify_mode