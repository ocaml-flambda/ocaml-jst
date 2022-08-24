(* TEST
  flags = "-extension Comprehensions"
*)

(******************************************************************************
 *                        ******** ATTENTION! ********                        *
 *                                                                            *
 * This file should be kept in sync with the file                             *
 * "list_comprehensions_side_effects.ml".  If you're adding a test to one,    *
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
  |> Array.map show_item
  |> Array.to_list
  |> String.concat "; "
  |> surround "[" "]"
;;

let show_as_tuple show_item xs =
  xs
  |> Array.map show_item
  |> Array.to_list
  |> String.concat ", "
;;

let out3 (i, j, k) = say "  %d, %d, %d;" i j k;;

let out6 (i, j, k, x, y, z) = say "  %d, %d, %d, %d, %d, %d;" i j k x y z;;

let report out f =
  let result = f () in
  say "";
  say "result = [|";
  Array.iter out result;
  say "|]"
;;

report out3 (fun () ->
  [| begin
       say ">>> i = %d, j = %d, k = %d" i j k;
       i, j, k
     end
       for k = (say ">> first (from)"; -1) downto (say ">> second (to)"; -3)
       when (say "> i = %d, j = %d | when even i" i j; i mod 2 = 0)
       for i = (say "first (from)"; 0) to (say "second (to)"; 3)
       and j in (say "third (in)"; [|10;20;30|])
  |]
)
;;

say "";;

report out3 (fun () ->
  [| begin
       say ">>> i = %d, j = %d, k = %d" i j k;
       i, j, k
     end
       for i = (say "first (from)"; 0) to (say "second (to)"; 3)
       and j in (say "third (in)"; [|10;20;30|])
       and k = (say "fourth (downfrom)"; 100) downto (say "fifth (downto)"; 97)
  |]
)
;;

say "";;

report out6 (fun () ->
  [| begin
       say ">>> i = %d, j = %d, k = %d, x = %d, y = %d, z = %d" i j k x y z;
       i, j, k, x, y, z
     end
       for x = (say "> first (downfrom)"; 1) downto (say "> second (downto)"; 0)
       and y in (say "> third (in)"; [|20;10|])
       and z = (say "> fourth (from)"; 99) to (say "> fifth (to)"; 100)
       for i = (say "first (from)"; 0) to (say "second (to)"; 1)
       and j in (say "third (in)"; [|10;20|])
       and k = (say "fourth (downfrom)"; 100) downto (say "fifth (downto)"; 99)
  |]
)
;;
