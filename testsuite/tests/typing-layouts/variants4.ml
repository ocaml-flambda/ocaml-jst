type 'a1 fmtty_rel =
  | Char_ty : 'a1 fmtty_rel -> (char -> 'a1) fmtty_rel


(* let rec erase_rel : type a . a fmtty_rel -> a fmtty_rel = function
 *   | Char_ty rest -> Char_ty (erase_rel rest) *)

let rec erase_rel : 'b . 'b fmtty_rel -> 'b fmtty_rel =
  fun (type c) ->
  ((function
    | Char_ty rest -> Char_ty (erase_rel rest)) : c fmtty_rel -> c fmtty_rel)
