(* TEST
  flags = "-extension Comprehensions"
*)

(******************************************************************************
 *                        ******** ATTENTION! ********                        *
 *                                                                            *
 * This file should be kept in sync with the file                             *
 * "array_comprehensions_side_effects.ml".  If you're adding a test to one,   *
 * add it to the other as well; if the test output changes in one file and    *
 * not the other (except as documented in comments), this is a bug.           *
 ******************************************************************************)

(******************************************************************************)
(**** Test the order of evaluation ****)

let say fmt =
  Printf.kfprintf (fun stdout -> Printf.fprintf stdout "\n") stdout fmt
;;

let surround l r m = l ^ m ^ r;;

let show_list show_item xs =
  xs
  |> List.map show_item
  |> String.concat "; "
  |> surround "[" "]"
;;

let show_as_tuple show_item xs =
  xs
  |> List.map show_item
  |> String.concat ", "
;;

let report f =
  let result = f () in
  say "";
  say "result = [";
  List.iter (fun (i, j, k) -> say "  %d, %d, %d;" i j k) result;
  say "]"
;;

report (fun () ->
  [ begin
      say ">>> i = %d, j = %d, k = %d" i j k;
      i, j, k
    end
      for k = (say ">> first (from)"; -1) downto (say ">> second (to)"; -3)
      when (say "> i = %d, j = %d | when even i" i j; i mod 2 = 0)
      for i = (say "first (from)"; 0) to (say "second (to)"; 3)
      and j in (say "third (and)"; [10;20;30])
  ]
)
;;

say "";;

report (fun () ->
  [ begin
      say ">>> i = %d, j = %d, k = %d" i j k;
      i, j, k
    end
      for i = (say "first (from)"; 0) to (say "second (to)"; 3)
      and j in (say "third (and)"; [10;20;30])
      and k = (say "fourth (downfrom)"; 100) downto (say "fifth (downto)"; 97)
  ]
)
;;

