open Types

val one : unit_desc
val mul : unit_desc -> unit_desc -> unit_desc
val pow : int -> unit_desc -> unit_desc
val inv : unit_desc -> unit_desc
val norm : unit_desc -> unit_desc
val unify :
  (type_expr -> unit_desc -> unit) ->
  unit_desc -> unit_desc -> bool
val moregen :
  bool ->
  (type_expr -> bool) ->
  (type_expr -> unit_desc -> unit) ->
  (unit_desc * unit_desc) list -> bool
val eqtype :
  (type_expr * type_expr) list ->
  (unit_desc * unit_desc) list -> bool
