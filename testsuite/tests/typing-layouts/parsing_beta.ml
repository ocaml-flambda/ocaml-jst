(* TEST
   flags = "-extension layouts_beta"
   * toplevel
*)

type ('a : value) t0 = 'a list;;

type ('a : immediate) t0 = 'a list;;

type ('a : void) t0 = 'a list;;

type ('a : valu) t0 = 'a list;;

(* XXX layouts review: The " : immediate" here doesn't show up in the output.
   Probably we should fix that? *)
