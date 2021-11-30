(* TEST
   include ocamlcommon *)


let printf = Printf.printf

let test_printing () =
  let example =
    "[(j,i) for j = 0 to i when (i >= 4) && (j >= 4) for i = 0 to 9 when (i mod 2 = 0)]"
  in
  let expr = Parse.expression (Lexing.from_string example) in
  let reprint = Pprintast.string_of_expression expr in
  if reprint = example then
    printf "reprint ok\n"
  else
    printf "reprint error:\n%s\n  became\n%s\n" example reprint

let () = test_printing ()

let () = printf "\n-----\n\n"

let starts_with pfx str =
  String.length str >= String.length pfx
  &&
  String.sub str 0 (String.length pfx) = pfx

let test_iteration () =
  let example =
    "[ [%expr] for i = [%low] to [%high] when [%cond] ]"
  in
  let expr = Parse.expression (Lexing.from_string example) in
  let extension it ((name, _) : Parsetree.extension) =
    if not (starts_with "extension." name.txt) then
      Printf.printf "  %s\n" name.txt
  in
  let iterator =
    { Ast_iterator.default_iterator with extension }
  in
  Printf.printf "extensions found:\n";
  iterator.expr iterator expr

let () = test_iteration ()
