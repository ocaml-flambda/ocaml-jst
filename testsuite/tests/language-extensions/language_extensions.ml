(* TEST
   include ocamlcommon
   flags = "-I ${ocamlsrcdir}/parsing"
   reference = "${test_source_directory}/reference.txt"
*)

(* Currently, this test case only works with modular extensions, as they fail
   during parsing and we test via parsing. *)

(* Change these two variables to change which extension is being tested *)
let extension            = Clflags.Extension.Comprehensions
let extension_expression = "[x for x = 1 to 10]"

let extension_name = Clflags.Extension.to_string extension

let report ~name ~text =
  Printf.printf "# %s [%s %s]:\n%s\n\n"
    name
    extension_name
    (if Clflags.Extension.is_enabled extension then "enabled" else "disabled")
    text

let parse_with_extension ?(full_name = false) name =
  let expr = match Parse.expression (Lexing.from_string extension_expression) with
    | expr -> Some expr
    | exception (Extensions_parsing.Error.Error _) -> None
  in
  report
    ~name:(if full_name
           then name
           else "\"" ^ extension_name ^ "\" extension " ^ name)
    ~text:(Option.fold
             ~none:"<syntax error>" ~some:Pprintast.string_of_expression expr)
;;

let should_succeed name what f =
  report ~name ~text:(match f () with
    | () ->
        "Succeeded at " ^ what
    | exception Arg.Bad msg ->
        "FAILED at " ^ what ^ ", with the following error\n:" ^ msg)
;;

let should_fail name f =
  report ~name ~text:(match f () with
    | () -> "<succeeded INCORRECTLY>"
    | exception Arg.Bad msg -> "Failed as expected: " ^ msg)
;;

let try_disallowing_extensions name =
  should_succeed
    name
    "disallowing all extensions"
    Clflags.Extension.disallow_extensions
;;

type goal = Fail | Succeed

let when_disallowed goal f_str f =
  let can_or_can't = match goal with
    | Fail    -> "can't"
    | Succeed -> "can"
  in
  let f_code = "[" ^ f_str ^ "]" in
  let name =
    can_or_can't ^ " call " ^ f_code ^ " when extensions are disallowed"
  in
  let action () = f extension in
  match goal with
  | Fail    -> should_fail    name                                   action
  | Succeed -> should_succeed name ("redundantly calling " ^ f_code) action
;;

let lift_with with_fn extension = with_fn extension Fun.id;;

(* Test the ground state *)

parse_with_extension "in its default state";

(* Disable all extensions for testing *)

List.iter Clflags.Extension.disable Clflags.Extension.all;
parse_with_extension ~full_name:true "no extensions enabled";

(* Test globally toggling a language extension *)

Clflags.Extension.enable extension;
parse_with_extension "enabled";

Clflags.Extension.enable extension;
parse_with_extension "still enabled";

Clflags.Extension.disable extension;
parse_with_extension "disabled";

Clflags.Extension.disable extension;
parse_with_extension "still disabled";

Clflags.Extension.set extension ~enabled:true;
parse_with_extension "enabled via [set]";

Clflags.Extension.enable extension;
parse_with_extension "still enabled, via [set] and [enable]";

Clflags.Extension.set extension ~enabled:false;
parse_with_extension "disabled via [set]";

Clflags.Extension.disable extension;
parse_with_extension "still disabled, via [set] and [disable]";

(* Test locally toggling a language extension *)

(* Globally disable the language extension (idempotent, given the prior tests,
   but it's more robust to do this explicitly) *)
Clflags.Extension.disable extension;

Clflags.Extension.with_enabled extension (fun () ->
  parse_with_extension "enabled locally and disabled globally");

Clflags.Extension.with_disabled extension (fun () ->
  parse_with_extension "disabled locally and globally");

Clflags.Extension.with_set extension ~enabled:true (fun () ->
  parse_with_extension "enabled locally via [with_set] and disabled globally");

Clflags.Extension.with_set extension ~enabled:false (fun () ->
  parse_with_extension "disabled locally via [with_set] and also globally");

(* Globally enable the language extension *)
Clflags.Extension.enable extension;

Clflags.Extension.with_disabled extension (fun () ->
  parse_with_extension "disabled locally and enabled globally");

Clflags.Extension.with_enabled extension (fun () ->
  parse_with_extension "enabled locally and globally");

Clflags.Extension.with_set extension ~enabled:false (fun () ->
  parse_with_extension "disabled locally via [with_set] and enabled globally");

Clflags.Extension.with_set extension ~enabled:true (fun () ->
  parse_with_extension "disabled locally via [with_set] and also globally");

(* Test disallowing extensions *)

try_disallowing_extensions
  "can disallow extensions while extensions are enabled";

try_disallowing_extensions
  "can disallow extensions while extensions are already disallowed";

(* Test that disallowing extensions prevents other functions from working *)

when_disallowed Fail "set ~enabled:true"
  (Clflags.Extension.set ~enabled:true);

when_disallowed Succeed "set ~enabled:false"
  (Clflags.Extension.set ~enabled:false);

when_disallowed Fail "enable"
  Clflags.Extension.enable;

when_disallowed Succeed "disable"
  Clflags.Extension.disable;

when_disallowed Fail "with_set ~enabled:true"
  (Clflags.Extension.with_set ~enabled:true |> lift_with);

when_disallowed Succeed "with_set ~enabled:false"
  (Clflags.Extension.with_set ~enabled:false |> lift_with);

when_disallowed Fail "with_enabled"
  (Clflags.Extension.with_enabled |> lift_with);

when_disallowed Succeed "with_disabled"
  (Clflags.Extension.with_disabled |> lift_with);

(* Test explicitly (rather than just via [report]) that [is_enabled] returns
   [false] now that we've disallowed all extensions *)
report
  ~name:"[is_enabled] returns [false] when extensions are disallowed"
  ~text:("\"" ^ extension_name ^ "\" is " ^
         if Clflags.Extension.is_enabled extension
         then "INCORRECTLY enabled"
         else "correctly disabled")
