(* TEST
   include ocamlcommon
   flags = "-I ${ocamlsrcdir}/parsing"
   reference = "${test_source_directory}/reference.txt"
*)

let report ~name ~text =
  Printf.printf "# %s [local %s]:\n%s\n\n"
    name
    (if Clflags.Extension.is_enabled Local then "enabled" else "disabled")
    text

let parse_local name =
  let example =
    "fun (local_ x) -> x"
  in
  let expr = match Parse.expression (Lexing.from_string example) with
    | expr -> Some expr
    | exception (Syntaxerr.Error _) -> None
  in
  report
    ~name
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

parse_local "no extensions enabled";

(* Test globally toggling [Local] *)

Clflags.Extension.enable Local;
parse_local "\"local\" extension enabled";

Clflags.Extension.enable Local;
parse_local "\"local\" extension still enabled";

Clflags.Extension.disable Local;
parse_local "\"local\" extension disabled";

Clflags.Extension.disable Local;
parse_local "\"local\" extension still disabled";

Clflags.Extension.set Local ~enabled:true;
parse_local "\"local\" extension enabled via [set]";

Clflags.Extension.enable Local;
parse_local "\"local\" extension still enabled, via [set] and [enable]";

Clflags.Extension.set Local ~enabled:false;
parse_local "\"local\" extension disabled via [set]";

Clflags.Extension.disable Local;
parse_local "\"local\" extension still disabled, via [set] and [disable]";

(* Test locally toggling [Local] *)

(* Globally disable [Local] (idempotent, but more robust) *)
Clflags.Extension.disable Local;

Clflags.Extension.with_enabled Local (fun () ->
  parse_local "\"local\" extension enabled locally and disabled globally");

Clflags.Extension.with_disabled Local (fun () ->
  parse_local "\"local\" extension disabled locally and globally");

Clflags.Extension.with_set Local ~enabled:true (fun () ->
  parse_local
    "\"local\" extension enabled locally via [with_set] and disabled globally");

Clflags.Extension.with_set Local ~enabled:false (fun () ->
  parse_local
    "\"local\" extension disabled locally via [with_set] and also globally");

(* Globally enable [Local] *)
Clflags.Extension.enable Local;

Clflags.Extension.with_disabled Local (fun () ->
  parse_local "\"local\" extension disabled locally and enabled globally");

Clflags.Extension.with_enabled Local (fun () ->
  parse_local "\"local\" extension enabled locally and globally");

Clflags.Extension.with_set Local ~enabled:false (fun () ->
  parse_local
    "\"local\" extension disabled locally via [with_set] and enabled globally");

Clflags.Extension.with_set Local ~enabled:true (fun () ->
  parse_local
    "\"local\" extension disabled locally via [with_set] and also globally");

(* Test disallowing extensions *)

Clflags.Extension.enable Local;
try_disallowing_extensions
  "can't disallow extensions while an extension is enabled";

Clflags.Extension.disable Local;
try_disallowing_extensions
  "can disallow extensions while no extensions are enabled";

try_disallowing_extensions
  "can disallow extensions while extensions are already disallowed";

(* Test that disallowing extensions prevents other functions from working *)

should_fail
  "can't call [set ~enabled:true] when extensions are disallowed"
  (fun () -> Clflags.Extension.set Local ~enabled:true);

should_fail
  "can't call [set ~enabled:false] when extensions are disallowed"
  (fun () -> Clflags.Extension.set Local ~enabled:false);

should_fail
  "can't call [enable] when extensions are disallowed"
  (fun () -> Clflags.Extension.enable Local);

should_fail
  "can't call [disable] when extensions are disallowed"
  (fun () -> Clflags.Extension.disable Local);

should_fail
  "can't call [with_set ~enabled:true] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_set Local ~enabled:true Fun.id);

should_fail
  "can't call [with_set ~enabled:false] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_set Local ~enabled:false Fun.id);

should_fail
  "can't call [with_enabled] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_enabled Local Fun.id);

should_fail
  "can't call [with_disabled] when extensions are disallowed"
  (fun () -> Clflags.Extension.with_disabled Local Fun.id);

(* Test explicitly (rather than just via [report]) that [is_enabled] returns
   [false] now that we've disallowed all extensions *)
report
  ~name:"[is_enabled] returns [false] when extensions are disallowed"
  ~text:(if Clflags.Extension.is_enabled Local
         then "\"local\" is INCORRECTLY enabled"
         else "\"local\" is correctly disabled")
