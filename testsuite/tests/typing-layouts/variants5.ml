
type 'a foo =
  | Format_arg_ty : 'b foo -> ('b foo -> int) foo

let rec bprint_fmtty : type a. a foo -> unit =
  fun fmtty -> match fmtty with
  | Format_arg_ty sub_fmtty -> bprint_fmtty sub_fmtty

(* Parsed as: *)

(* let rec bprint_fmtty : 'a foo -> unit =
 *   fun (type a) ->
 *   ((fun fmtty -> match fmtty with
 *      | Format_arg_ty sub_fmtty -> bprint_fmtty sub_fmtty)
 *    : a foo -> unit) *)

