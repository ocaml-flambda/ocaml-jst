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

  type 'a failure_data =
    | Data      of 'a
    | Exception of exn

  type ('a, 'b) failure =
    { counterexample : 'a
    ; data           : 'b failure_data
    ; tests          : int
    ; shrinks        : int }

  type ('a, 'b) result =
    | Passed
    | Failed  of ('a, 'b) failure

  let rec find_counterexample prop = function
    | [] -> None
    | x :: xs ->
        match prop x with
        | OK               -> find_counterexample prop xs
        | Failed_with data -> Some (x, Data data)
        | exception exn    -> Some (x, Exception exn)

  let rec minimize shrink prop failure =
    match find_counterexample prop (shrink failure.counterexample) with
    | Some (counterexample, data) ->
        minimize shrink prop
          { failure with counterexample; data; shrinks = failure.shrinks + 1 }
    | None ->
        failure

  let test (type a b) n gen shrink prop =
    let exception Counterexample of (a, b) failure in
    match
      for tests = 1 to n do
        let x = gen () in
        let stop_with_this_counterexample data =
          raise (Counterexample
                   { counterexample = x; data = data; tests; shrinks = 0 })
        in
        match prop x with
        | OK               -> ()
        | Failed_with data -> stop_with_this_counterexample (Data      data)
        | exception exn    -> stop_with_this_counterexample (Exception exn)
      done
    with
    | ()                               -> Passed
    | exception Counterexample failure -> Failed (minimize shrink prop failure)

  module Generator = struct
    let replicateG n g =
      Array.make n Fun.id |> Array.to_list |> List.map (fun _ -> g ())

    let pick_without_replacement xs =
      let rec go i xs = match i, xs with
        | 0, x :: xs -> x, xs
        | i, x :: xs -> let y, ys = go (i-1) xs
                        in y, x :: ys
        | _, []      -> assert false
      in
      go (Random.int (List.length xs)) xs

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

    let equal = String.equal
    module Set = Set.Make(String)

    let vars =
      List.init 26 (fun i -> String.make 1 (Char.chr (Char.code 'a' + i)))
    let wildcard = "_"
    let pattern_vars = wildcard :: vars
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

  (* We assume the body is a tuple of all the variables in the environment *)
  type t = { env : Var.Set.t ; clauses : clause list }

  module Generator = struct
    open QuickCheck.Generator

    let iterator () =
      if Random.bool ()
      then Range { start     = small_int ()
                 ; direction = if Random.bool () then To else Downto
                 ; stop      = small_int () }
      else Sequence (replicateG (Random.int 11) small_int)

    let predicate () =
      match Random.int 5 with
      | 0 -> Positive
      | 1 -> Negative
      | 2 -> Nonzero
      | 3 -> Even
      | 4 -> Odd
      | _ -> assert false

    (* Generates bindings that don't share variables *)
    let bindings sz =
      let rec go ~bindings ~available ~used = function
        | 0 ->
            (* We reverse the list because [_] becomes slightly more likely for
               later-generated values, and this shifts them towards the end of
               the for-and clause *)
            List.rev bindings, used
        | n ->
            let var, available = pick_without_replacement available in
            let available, used =
              if Var.equal var Var.wildcard
              then Var.wildcard :: available, used
              else available, Var.Set.add var used
            in
            let bindings = { var; iterator = iterator () } :: bindings in
            go ~bindings ~available ~used (n-1)
      in
      go
        ~bindings:[]
        ~available:Var.pattern_vars
        ~used:Var.Set.empty
        (Random.int sz + 1)

    let clause env sz =
      if not (Var.Set.is_empty env) && Random.int 4 < 1 then
        When(predicate (), pick (Var.Set.elements env)), env
      else
        let bs, env' = bindings sz in
        For bs, Var.Set.union env env'

    let comprehension () =
      let clause_n = Random.int 5 + 1 (* [1,5] *) in
      let for_max  = (7 - clause_n) (* [2,6] *) in
      let rec go env i =
        if i = clause_n then
          [], env
        else
          let b,  env'  = clause env for_max in
          let bs, env'' = go (Var.Set.union env env') (i+1) in
          b :: bs, env''
      in
      let clauses, env = go Var.Set.empty 0 in
      {env; clauses}
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

    let bindings_env bs =
      bs
      |> List.filter_map (function
        | {var = "_"; _} -> None
        | {var; _}       -> Some var)
      |> Var.Set.of_list

    let comprehension {env = _; clauses} =
      List.filter_map
        (fun clauses ->
           (* Brute force to figure out the deleted bindings *)
           let env, oclauses =
             List.fold_left_map
               (fun env clause ->
                  match clause with
                  | When (p,x) when not (Var.Set.mem x env) -> env, None
                  | When _ -> env, Some clause
                  | For bs -> bindings_env bs, Some clause)
               Var.Set.empty
               clauses
           in
           match List.filter_map Fun.id oclauses with
           | []      -> None
           | clauses -> Some {env; clauses})
        (nonempty_list clause clauses)

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
            let seq = seq
                      |> List.map Int.to_string
                      |> String.concat sep
                      |> sequence o
            in
            tokens ["in"; seq]
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

    let comprehension o {env; clauses} =
      let clauses = if ocaml o then List.rev clauses else clauses in
      sequence o
        (tokens
          (tuple (Var.Set.elements env) :: List.map (clause o) clauses))
  end

  let generator = Generator.comprehension
  let shrinker  = Shrinker.comprehension
  let to_string = To_string.comprehension
end

module Interactive_command = struct
  let command cmd args ~setup ~input ~output ~f =
    let inch, outch =
      Unix.open_process_args cmd (Array.of_list (cmd :: args))
    in
    let output str = Util.output_line outch (output str) in
    let interact str =
      output str;
      input inch
    in
    let cleanup () = ignore (Unix.close_process (inch, outch)) in
    match setup output; f interact with
    | result      -> cleanup (); result
    | exception e -> cleanup (); raise e

  (* This is necessary because long lists cause the default printer to stack
     overflow.  It gets the indentation wonky, but that doesn't really matter
     here *)
  let ocaml_code_pp_list_as_python = {|
    let pp_list pp_elt fmt xs =
      let buf = Buffer.create 256 in
      let fbuf = Format.formatter_of_buffer buf in
      Format.pp_set_max_indent fbuf Int.max_int;
      let rec fill_buf prefix = function
        | x :: xs ->
            Format.fprintf fbuf "%s%a" prefix pp_elt x;
            fill_buf ", " xs
        | [] ->
            Format.pp_print_flush fbuf ();
      in
      Buffer.add_char buf '[';
      fill_buf "" xs;
      Buffer.add_char buf ']';
      Format.fprintf fmt "%s" (Buffer.contents buf)
    |}

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
      ~setup:(fun output ->
        output ("#print_length " ^ Int.to_string Int.max_int);
        output ocaml_code_pp_list_as_python;
        output "#install_printer pp_list")
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

  let main_comprehensions_agree ?(seed = Util.random_seed()) max_tests =
    Random.full_init seed;
    match test_comprehensions_agree max_tests with
    | Passed ->
        print_endline ("OK, passed " ^ Int.to_string max_tests ^ " tests.")
    | Failed { counterexample; data; tests; shrinks } ->
        let what, print_result_for, print_extra_information = match data with
          | Data data     ->
              "Counterexample",
              (fun ~output_prefix o ->
                 print_endline (output_prefix ^ "  = " ^ output_for o data)),
              (fun () -> ())
          | Exception exn ->
              "Exception",
              (fun ~output_prefix:_ _ -> ()),
              (fun () ->
                 Format.printf "  Exception:\n    %s\n"
                   (exn
                    |> Printexc.to_string
                    |> Str.global_replace (Str.regexp "\n") "\n    "))
        in
        let print_comprehension tag align o =
          let spaced_out s  = String.make (String.length s) ' ' in
          let input_prefix  = "  " ^ tag            ^ ": " ^ align in
          let output_prefix = "  " ^ spaced_out tag ^ "  " ^ align in
          print_endline
            (input_prefix  ^ Comprehension.to_string o counterexample);
          print_result_for ~output_prefix o
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
        print_comprehension "Python" "     " Python;
        print_extra_information ()
end

let () = Main.main_comprehensions_agree 1_000
