(* -*- compile-command: "ocamlc str.cma unix.cma quickcheck_lists_arrays_python.ml -o quickcheck-lists-arrays-python && ./quickcheck-lists-arrays-python"; -*- *)

module No_polymorphic_compare = struct
  let ( = )      = Int.equal
  let ( < )  x y = Int.compare x y <  0
  let ( > )  x y = Int.compare x y >  0
  let ( <= ) x y = Int.compare x y <= 0
  let ( >= ) x y = Int.compare x y >= 0
end

open No_polymorphic_compare

module Util = struct
  let rec take_while p = function
    | x :: xs when p x -> x :: take_while p xs
    | _ -> []

  let guard c x = if c then [x] else []

  (* For repeatability *)
  external random_seed : unit -> int array = "caml_sys_random_seed"

  let output_line oc str = begin
    output_string oc str;
    output_char oc '\n';
    flush oc
  end
end

module QuickCheck = struct
  type 'a prop_result =
    | OK
    | Failed_with of 'a

  type ('a, 'b) failure =
    { counterexample : 'a
    ; data           : 'b
    ; tests          : int
    ; shrinks        : int }

  type 'a crash =
    { crashexample : 'a
    ; exception_   : exn
    ; tests        : int }

  type ('a, 'b) result =
    | Passed
    | Failed  of ('a, 'b) failure
    | Crashed of 'a crash

  (* This swallows exceptions, which I *think* is OK *)
  let rec find_counterexample prop = function
    | [] -> None
    | x :: xs ->
        match prop x with
        | Failed_with data -> Some (x, data)
        | OK | exception _ -> find_counterexample prop xs

  let rec minimize shrink prop failure =
    match find_counterexample prop (shrink failure.counterexample) with
    | Some (counterexample, data) ->
        minimize shrink prop
          { failure with counterexample; data; shrinks = failure.shrinks + 1 }
    | None | exception _ ->
        failure

  let test (type a b) n gen shrink prop =
    let exception Counterexample of (a, b) failure in
    let exception Crashexample   of a crash in
    match
      for tests = 1 to n do
        let x = gen () in
        match prop x with
        | OK -> ()
        | Failed_with data ->
            raise (Counterexample
                     (minimize shrink prop
                        { counterexample = x; data; tests; shrinks = 0 }))
        | exception exception_ ->
            raise (Crashexample { crashexample = x; exception_; tests })
      done
    with
    | ()                               -> Passed
    | exception Counterexample failure -> Failed  failure
    | exception Crashexample   failure -> Crashed failure

  module Generator = struct
    let replicateG n g =
      Array.make n Fun.id |> Array.to_list |> List.map (fun _ -> g ())

    let pick xs =
      List.nth xs (Random.int (List.length xs))

    let small_int () = Random.int 11 - 5 (* [-5,5] *)
  end

  module Shrinker = struct
    let rec del1_and_shrink1 shrink = function
      | [] -> [], []
      | x :: xs ->
          let del, shrunk = del1_and_shrink1 shrink xs in
          ( xs :: List.map (fun xs' -> x :: xs') del
          , List.map (fun x'  -> x' :: xs)  (shrink x) @
            List.map (fun xs' -> x  :: xs') shrunk )

    let nonempty_list shrink xs =
      let del, shrunk = del1_and_shrink1 shrink xs in
      List.filter (function [] -> false | _ :: _ -> true) del @ shrunk

    let list shrink = function
      | [] -> []
      | xs ->
          let del, shrunk = del1_and_shrink1 shrink xs in
          [] :: (del @ shrunk)

    (* From Haskell's QuickCheck: make it positive, 0, then smaller by jumping
       half the distance each time *)
    let int i =
      let rec halves = function
        | 0 -> []
        | d -> i - d :: halves (d/2)
      in
      Util.guard (i < 0 && i <> Int.min_int) (-i) @
      Util.guard (i <> 0)                    0    @
      halves (i/2)

    (* Allow either one or two shrinks from the given shrinker *)
    let shrink2 shrink x =
      let shrink1 = shrink x in
      shrink1 @ List.concat_map shrink shrink1
  end
end

module Comprehension = struct
  module Var = struct
    type t = string
    module Set = Set.Make(String)

    let pattern_vars =
      let a = Char.code 'a' in
      "_" :: List.init 26 (fun i -> String.make 1 (Char.chr (a + i)))
  end

  type direction =
    | To
    | Downto

  type iterator =
    | Range    of { start : int; direction : direction; stop : int }
    | Sequence of int list

  type binding = { var : Var.t; iterator : iterator }

  type predicate =
    | Positive
    | Negative
    | Nonzero
    | Even
    | Odd

  let all_predicates = [Positive; Negative; Nonzero; Even; Odd]

  type clause =
    | For  of binding list
    | When of predicate * Var.t

  (* We assume the body is a tuple of all the variables *)
  type t = { vars : Var.Set.t ; clauses : clause list }

  module Generator = struct
    open QuickCheck.Generator

    let var () = pick Var.pattern_vars

    let iterator () =
      if Random.bool ()
      then Range { start     = small_int ()
                 ; direction = if Random.bool () then To else Downto
                 ; stop      = small_int () }
      else Sequence (replicateG (Random.int 11) small_int)

    let binding () = { var = var (); iterator = iterator () }

    let predicate () =
      match Random.int 5 with
      | 0 -> Positive
      | 1 -> Negative
      | 2 -> Nonzero
      | 3 -> Even
      | 4 -> Odd
      | _ -> assert false

    let bindings_vars bs =
      bs
      |> List.filter_map (function
        | {var = "_"; _} -> None
        | {var; _}       -> Some var)
      |> Var.Set.of_list

    let bindings sz =
      let bs = replicateG (Random.int sz + 1) binding in
      bs, bindings_vars bs

    let clause vars sz =
      if not (Var.Set.is_empty vars) && Random.int 4 < 1 then
        When(predicate (), pick (Var.Set.elements vars)), vars
      else
        let bs, vars' = bindings sz in
        For bs, Var.Set.union vars vars'

    let comprehension () =
      let clause_n = Random.int 5 + 1 (* [1,5] *) in
      let for_max  = (7 - clause_n) (* [2,6] *) in
      let rec go vars i =
        if i = clause_n then
          [], vars
        else
          let b,  vars' = clause vars for_max in
          let bs, vars'' = go (Var.Set.union vars vars') (i+1) in
          b :: bs, vars''
      in
      let clauses, vars = go Var.Set.empty 0 in
      {vars; clauses}
  end

  module Shrinker = struct
    open QuickCheck.Shrinker

    let pattern_var x = Util.take_while (fun p -> x <> p) Var.pattern_vars

    let iterator = function
      | Range { start; direction; stop } ->
          Util.guard
            (match direction with Downto -> true | To -> false)
            (Range { start = stop; direction = To; stop = start }) @
          List.map (fun start -> Range { start; direction; stop }) (int start) @
          List.map (fun stop  -> Range { start; direction; stop }) (int stop)
      | Sequence seq ->
          List.map (fun seq -> Sequence seq) (list int seq)

    let binding ({var = x; iterator = i} as b) =
      List.map (fun iterator -> {b with iterator}) (iterator    i) @
      List.map (fun var      -> {b with var})      (pattern_var x)

    let predicate p =
      Util.take_while (fun p' -> p <> p') all_predicates

    let clause = function
      | For bs     -> List.map (fun bs -> For bs)     (nonempty_list binding bs)
      | When(p, x) -> List.map (fun p  -> When(p, x)) (predicate p)

    let comprehension {vars = _; clauses} =
      List.filter_map (fun clauses ->
        (* Brute force to figure out the deleted bindings *)
        let vars, oclauses =
          List.fold_left_map
            (fun vars clause ->
               match clause with
               | When (p,x) when not (Var.Set.mem x vars) -> vars, None
               | When _ -> vars, Some clause
               | For bs -> Generator.bindings_vars bs, Some clause)
            Var.Set.empty
            clauses
        in
        match List.filter_map Fun.id oclauses with
        | [] -> None
        | clauses -> Some {vars; clauses}
      ) (nonempty_list clause clauses)

    (* Shrinking twice simplifies both bugs this found on its first go-round,
       since it can shrink both the endpoints of a to/downto range and it can
       shrink two parallel variable names at once. *)
    let comprehension = QuickCheck.Shrinker.shrink2 comprehension
  end

  module To_string = struct
    type format = OCaml_list | OCaml_array | Python

    let surround o c s = o ^ s ^ c

    let parenthesize = surround "(" ")"
    let bracket      = surround "[" "]"
    let spaced       = surround " " " "

    let tokens = String.concat " "

    let tuple = function
      | [tok] -> tok
      | toks  -> toks |> String.concat ", " |> parenthesize

    let ocaml = function
      | OCaml_list | OCaml_array -> true
      | Python -> false

    let sequence = function
      | OCaml_list | Python -> bracket
      | OCaml_array         -> surround "[|" "|]"

    let mod_ o = if ocaml o then "mod" else "%"
    let eq   o = if ocaml o then "="   else "=="
    let neq  o = if ocaml o then "<>"  else "!="

    let predicate o = function
      | Positive -> "> 0"
      | Negative -> "< 0"
      | Nonzero  -> tokens [neq o; "0"]
      | Even     -> tokens [mod_ o; "2"; eq o; "0"]
      | Odd      -> tokens [mod_ o; "2"; eq o; "0"]

    let ocaml_direction = function
      | To     -> "to"
      | Downto -> "downto"

    let python_binding seq =
      "in " ^ seq

    let binding o {var; iterator} =
      let iter = match iterator with
        | Range {start; direction; stop} ->
            if ocaml o then
              tokens [ "="
                     ; Int.to_string start
                     ; ocaml_direction direction
                     ; Int.to_string stop ]
            else
              let start, stop, step = match direction with
                | To     -> start, stop+1, []
                | Downto -> start, stop-1, ["-1"]
              in
              python_binding
                ("range"
                 ^ tuple ([Int.to_string start; Int.to_string stop] @ step))
        | Sequence seq ->
            let sep = (if ocaml o then ";" else ",") ^ " " in
            tokens
              [ "in"
              ; seq |> List.map Int.to_string |> String.concat sep |> sequence o ]
      in
      tokens [var; iter]

    let clause o = function
      | For bindings ->
          tokens [ "for"
                 ; bindings
                   |> List.map (binding o)
                   |> String.concat (if ocaml o then " and " else " for ") ]
      | When(pred, x) ->
          tokens [(if ocaml o then "when" else "if"); x; predicate o pred]

    let comprehension o {vars; clauses} =
      let clauses = if ocaml o then List.rev clauses else clauses in
      sequence o
        (tokens
          (tuple (Var.Set.elements vars) :: List.map (clause o) clauses))
  end

  let generator = Generator.comprehension
  let shrinker  = Shrinker.comprehension
  let to_string = To_string.comprehension
end

module Interactive_command = struct
  let command cmd args ~setup ~input ~output ~f =
    let inch, outch = Unix.open_process_args cmd (Array.of_list (cmd :: args)) in
    let output str = Util.output_line outch (output str) in
    let interact str =
      output str;
      input inch
    in
    let cleanup () = ignore (Unix.close_process (inch, outch)) in
    match setup output; f interact with
    | result      -> cleanup (); result
    | exception e -> cleanup (); raise e

  let input_ocaml_list_or_array_as_python_list i =
    let input = Buffer.create 16 in
    let rec input_lines () =
      let line = input_line i in
      Buffer.add_string input line;
      if not (String.contains line ']') then input_lines ()
    in
    input_lines ();
    let raw_list = Buffer.contents input in
    let start = String.index  raw_list '[' in
    let stop  = String.rindex raw_list ']' in
    let list  = String.sub raw_list start (stop - start + 1) in
    list
    |> Str.global_replace (Str.regexp "[ \n]+") " "
    |> Str.global_replace (Str.regexp "|")      ""
    |> Str.global_replace (Str.regexp ";")      ","

  let ocaml ~f =
    command
      "../../../ocaml"
      [ "-extension"; "comprehensions"
      ; "-noprompt"; "-no-version"
      ; "-w"; "no-unused-var" ]
      ~setup:(fun output -> output ("#print_length " ^ Int.to_string Int.max_int))
      ~input:input_ocaml_list_or_array_as_python_list
      ~output:(fun str -> str ^ ";;")
      ~f

  let python ~f =
    command
      "/usr/bin/python3"
      ["-qic"; "import sys\nsys.ps1 = ''"]
      ~setup:(Fun.const ())
      ~input:input_line
      ~output:Fun.id
      ~f
end

module Main = struct
  type output = { ocaml_list  : string
                ; ocaml_array : string
                ; python      : string }

  let output_for o output =
    match (o : Comprehension.To_string.format) with
    | OCaml_list  -> output.ocaml_list
    | OCaml_array -> output.ocaml_array
    | Python      -> output.python

  let test_comprehensions_agree max_tests =
    let ( = ) = String.equal in
    Interactive_command.ocaml ~f:(fun ocaml ->
      Interactive_command.python ~f:(fun python ->
        QuickCheck.test max_tests Comprehension.generator Comprehension.shrinker
          (fun c ->
             let ocaml_list  = ocaml  (Comprehension.to_string OCaml_list  c) in
             let ocaml_array = ocaml  (Comprehension.to_string OCaml_array c) in
             let python      = python (Comprehension.to_string Python      c) in
             if ocaml_list = ocaml_array && ocaml_array = python
             then OK
             else Failed_with {ocaml_list; ocaml_array; python})))

  let print_failure_or_crash ~what ~seed ~comprehension ~data ~tests ~shrinks =
    let print_comprehension tag align o =
      let spaced_out s  = String.make (String.length s) ' ' in
      let input_prefix  = "  " ^ tag            ^ ": " ^ align in
      let output_prefix = "  " ^ spaced_out tag ^ "  " ^ align in
      print_endline (input_prefix  ^ Comprehension.to_string o comprehension);
      Option.iter
        (fun data -> print_endline (output_prefix ^ "  = " ^ output_for o data))
        data
    in
    let seed_guts =
      seed |> Array.map Int.to_string |> Array.to_list |> String.concat "; "
    in
    let n_tests = match tests with
      | 1 -> "1 test"
      | _ -> Int.to_string tests ^ " tests"
    in
    let and_k_shrinks = match shrinks with
      | 0 -> ""
      | 1 -> " and 1 shrink"
      | _ -> " and " ^ Int.to_string shrinks ^ " shrinks"
    in
    Format.printf "Failed with seed [|%s|]!\n" seed_guts;
    Format.printf "%s (after %s%s):\n" what n_tests and_k_shrinks;
    print_comprehension "OCaml list" " " OCaml_list;
    print_comprehension "OCaml array" "" OCaml_array;
    print_comprehension "Python" "     " Python

  let main_comprehensions_agree ?(seed = Util.random_seed()) max_tests =
    Random.full_init seed;
    match test_comprehensions_agree max_tests with
    | Passed ->
        print_endline ("OK, passed " ^ Int.to_string max_tests ^ " tests.")
    | Failed { counterexample; data; tests; shrinks } ->
        print_failure_or_crash
          ~what:"Counterexample"
          ~seed
          ~comprehension:counterexample
          ~data:(Some data)
          ~tests
          ~shrinks
    | Crashed { crashexample; exception_; tests } ->
        print_failure_or_crash
          ~what:"Exception"
          ~seed
          ~comprehension:crashexample
          ~data:None
          ~tests
          ~shrinks:0;
        Format.printf "  Exception:\n    %s\n"
          (exception_
           |> Printexc.to_string
           |> Str.global_replace (Str.regexp "\n") "\n    ")
end

let () = Main.main_comprehensions_agree 1_000
