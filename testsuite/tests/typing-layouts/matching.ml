type 'a fmtty =
  | String_ty of 'a fmtty
  | End_of_fmtty

let rec erase_rel : 'a fmtty -> 'a fmtty
= function
  | String_ty rest -> String_ty (erase_rel rest)
  | End_of_fmtty -> End_of_fmtty
