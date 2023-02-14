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

let try_disallowing_extensions name =
  report ~name ~text:(match Clflags.Extension.disallow_extensions () with
    | () ->
        "Successfully disallowed all extensions"
    | exception Arg.Bad msg ->
        "Failed to disallow all extensions, with the following error:\n" ^ msg)
;;

let should_fail name f =
  report ~name ~text:(match f () with
    | () -> "<succeeded unexpectedly>"
    | exception Arg.Bad msg -> "Failed: " ^ msg)
;;

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

Clflags.Extension.enable extension;
try_disallowing_extensions
  "can disallow extensions while extensions are enabled";

try_disallowing_extensions
  "can disallow extensions while extensions are already disallowed";

(* Test that disallowing extensions prevents other functions from working *)

should_fail
  "can't call [set ~enabled:true] when extensions are disallowed"
  (fun () -> Clflags.Extension.set extension ~enabled:true);

should_fail
  "can't call [set ~enabled:false] when extensions are disallowed"
  (fun () -> Clflags.Extension.set extension ~enabled:false);

should_fail
  "can't call [enable] when extensions are disallowed"
  (fun () -> Clflags.Extension.enable extension);

should_fail
  "can't call [disable] when extensions are disallowed"
  (fun () -> Clflags.Extension.disable extension);

should_fail
  "can't call [with_set ~enabled:true] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_set extension ~enabled:true Fun.id);

should_fail
  "can't call [with_set ~enabled:false] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_set extension ~enabled:false Fun.id);

should_fail
  "can't call [with_enabled] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_enabled extension Fun.id);

should_fail
  "can't call [with_disabled] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_disabled extension Fun.id);

(* Test explicitly (rather than just via [report]) that [is_enabled] returns
   [false] now that we've disallowed all extensions *)
report
  ~name:"[is_enabled] returns [false] when extensions are disallowed"
  ~text:("\"" ^ extension_name ^ "\" is " ^
         if Clflags.Extension.is_enabled extension
         then "INCORRECTLY enabled"
         else "correctly disabled")
