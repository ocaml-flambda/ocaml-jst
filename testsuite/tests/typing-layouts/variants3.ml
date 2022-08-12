(* This was wrong when existentials were being defaulted to value (in
   Ctype.instance_constructor.

  Nope actually that didn't fix it.*)

type 'a fmtty_rel =
  | Char_ty of 'a fmtty_rel

(* let rec erase_rel : type a . a fmtty_rel -> a fmtty_rel
 *   = fun x -> erase_rel x *)
let rec erase_rel : 'b . 'b fmtty_rel -> 'b fmtty_rel
  = fun (type c) -> ((fun x -> erase_rel x) : c fmtty_rel -> c fmtty_rel)
