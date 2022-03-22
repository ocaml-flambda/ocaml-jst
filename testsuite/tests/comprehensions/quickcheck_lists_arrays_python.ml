(* -*- compile-command: "ocamlopt -w +A-4-40-42-44 str.cmxa unix.cmxa quickcheck_lists_arrays_python.ml -o quickcheck-lists-arrays-python && ./quickcheck-lists-arrays-python"; -*- *)

module No_polymorphic_compare = struct
  let ( = )      = Int.equal
  let ( < )  x y = Int.compare x y <  0
  let ( > )  x y = Int.compare x y >  0
  let ( <= ) x y = Int.compare x y <= 0
  let ( >= ) x y = Int.compare x y >= 0
end

open No_polymorphic_compare

module Util = struct
  module List_monad = struct
    let pure x = [x]
    let bind xs f = List.concat_map f xs

    let (let*)      = bind
    let (let+) xs f = List.map f xs

    (* I think this is right *)
    let (and*) xs ys =
      let* x = xs in
      let+ y = ys in
      x,y
    let (and+) = (and*)

    let rec traverse f = function
      | [] ->
          pure []
      | x :: xs ->
          let+ y  = f x
          and+ ys = traverse f xs in
          y :: ys
  end

  let rec take_while p = function
    | x :: xs when p x -> x :: take_while p xs
    | _ -> []

  let guard c x = if c then [x] else []

  let max x y = if x > y then x else y

  let range_to start stop =
    List.init (max 0 (stop - start + 1)) (fun i -> start + i)

  let range_downto start stop =
    List.init (max 0 (start - stop + 1)) (fun i -> start - i)

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

    let small_int () = Random.int 7 - 3 (* [-3,3] *)
  end

  module Shrink = struct
    let rec del1_and_shrink1 shrink = function
      | [] ->
          [], []
      | x :: xs ->
          let del, shrunk = del1_and_shrink1 shrink xs in
          let cons_x xs' = x :: xs' in
          ( xs                                        :: List.map cons_x del
          , List.map (fun x'  -> x' :: xs) (shrink x) @  List.map cons_x shrunk
          )

    let nonempty_list shrink xs =
      match del1_and_shrink1 shrink xs with
      | [[]], shrunk -> shrunk
      | del,  shrunk -> del @ shrunk

    let list shrink xs =
      let del, shrunk = del1_and_shrink1 shrink xs in
      del @ shrunk

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

module Var : sig
  type t = string

  val equal : t -> t -> bool

  val vars : t list
  val wildcard : t
  val pattern_vars : t list
end = struct
  type t = string

  let equal = String.equal

  let vars =
    List.init 26 (fun i -> String.make 1 (Char.chr (Char.code 'a' + i)))
  let wildcard = "_"
  let pattern_vars = wildcard :: vars
end

module Environment : sig
  type t

  val empty : t
  val of_variables : Var.t list -> t

  val add   : Var.t -> t -> t
  val union : t -> t -> t

  val is_empty : t -> bool
  val is_bound : Var.t -> t -> bool
  val is_free  : Var.t -> t -> bool

  val variables     : t -> Var.t list
  val variables_seq : t -> Var.t Seq.t
end = struct
  include Set.Make(String)

  let of_variables  = of_list
  let is_bound      = mem
  let is_free x env = not (is_bound x env)
  let variables     = elements
  let variables_seq = to_seq
end

module Substitution : sig
  type binding =
    | Deleted
    | Renamed of Var.t

  type t

  val identity   : t
  val delete     : Var.t -> t
  val rename     : Var.t -> Var.t -> t
  val delete_env : Environment.t -> t
  val rename_env : Environment.t -> (Var.t -> Var.t) -> t

  val shadow_env : Environment.t -> t -> t

  val apply : t -> Var.t -> binding option
end = struct
  type binding =
    | Deleted
    | Renamed of Var.t

  include Map.Make(String)

  type nonrec t = binding t

  let identity   = empty
  let delete x   = singleton x Deleted
  let rename x y = singleton x (Renamed y)

  let create_with_env f env =
    of_seq (Seq.map (fun x -> x, f x) (Environment.variables_seq env))

  let delete_env = create_with_env (Fun.const Deleted)

  let rename_env env f = create_with_env (fun x -> Renamed (f x)) env

  let shadow_env env = filter (fun x _ -> Environment.is_free x env)

  let apply subst x = find_opt x subst
end

module Comprehension = struct
  type int_term =
    | Literal  of int
    | Variable of Var.t

  type direction =
    | To
    | Downto

  type iterator =
    | Range    of { start     : int_term
                  ; direction : direction
                  ; stop      : int_term  }
    | Sequence of int_term list

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
  type t = { env : Environment.t ; clauses : clause list }

  module Bound_vars = struct
    let bindings bs =
      bs |>
      List.filter_map (fun {var; iterator = _} ->
        if Var.equal var Var.wildcard
        then None
        else Some var) |>
      Environment.of_variables

    let clauses =
      List.fold_left
        (fun env -> function
           | For bs -> Environment.union (bindings bs) env
           | When _ -> env)
        Environment.empty
  end

  module Free_vars = struct
    let parallel_bindings bs =
      bs |>
      List.concat_map (fun {iterator; var = _} ->
        List.filter_map
          (function
            | Variable x -> Some x
            | Literal  _ -> None)
          (match iterator with
           | Range { start; direction = _; stop } -> [start; stop]
           | Sequence seq                         -> seq)) |>
      Environment.of_variables
  end

  module Generator = struct
    open QuickCheck.Generator

    let in_scope_var env = pick (Environment.variables env)

    let int_term env =
      if not (Environment.is_empty env) && Random.int 10 < 1 then
        Variable (in_scope_var env)
      else
        Literal (small_int ())

    let iterator env =
      if Random.bool ()
      then Range { start     = int_term env
                 ; direction = if Random.bool () then To else Downto
                 ; stop      = int_term env }
      else Sequence (replicateG (Random.int 8) (fun () -> int_term env))
      (* Both Ranges and Sequences can range from length 0 to 7 (inclusive),
         although with different probabilities *)

    let predicate () =
      match Random.int 5 with
      | 0 -> Positive
      | 1 -> Negative
      | 2 -> Nonzero
      | 3 -> Even
      | 4 -> Odd
      | _ -> assert false

    (* Generates bindings that don't share variables *)
    let bindings env sz =
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
              else available, Environment.add var used
            in
            let bindings = { var; iterator = iterator env } :: bindings in
            go ~bindings ~available ~used (n-1)
      in
      go
        ~bindings:[]
        ~available:Var.pattern_vars
        ~used:Environment.empty
        (Random.int sz + 1)

    let clause env sz =
      if not (Environment.is_empty env) && Random.int 4 < 1 then
        When(predicate (), in_scope_var env), env
      else
        let bs, env' = bindings env sz in
        For bs, Environment.union env env'

    let comprehension () =
      let clause_n = Random.int 5 + 1 (* [1,5] *) in
      let for_max  = (7 - clause_n) (* [2,6] *) in
      let rec go env i =
        if i = clause_n then
          [], env
        else
          let b,  env'  = clause env for_max in
          let bs, env'' = go (Environment.union env env') (i+1) in
          b :: bs, env''
      in
      let clauses, env = go Environment.empty 0 in
      {env; clauses}
  end

  module Shrink = struct
    open QuickCheck.Shrink

    (* [-3,3], in increasing order of "complexity" *)
     let all_small_ints =
      let pos = List.init 3 (( + ) 1) in
      let neg = List.map Int.neg pos in
      0 :: (pos @ neg)

    let all_small_int_lits = List.map (fun n -> Literal n) all_small_ints

    let pattern_var x = Util.take_while (fun p -> x <> p) Var.pattern_vars

    let int_term = function
      | Literal  n -> List.map (fun n -> Literal n) (int n)
      | Variable _ -> all_small_int_lits

    let iterator = function
      | Range { start; direction; stop } ->
          [Sequence [start]; Sequence [stop]] @
          Util.guard
            (match direction with Downto -> true | To -> false)
            (Range { start = stop; direction = To; stop = start }) @
          List.map
            (fun start -> Range { start; direction; stop })
            (int_term start) @
          List.map
            (fun stop  -> Range { start; direction; stop })
            (int_term stop) @
          (match start, stop with
           | Literal start, Literal stop ->
               let range = match direction with
                 | To     -> Util.range_to
                 | Downto -> Util.range_downto
               in
               [Sequence (List.map (fun n -> Literal n) (range start stop))]
           | Variable _, _ | _, Variable _ -> [])
      | Sequence seq ->
          List.map (fun seq -> Sequence seq) (list int_term seq)

    let binding ({var = x; iterator = i} as b) =
      List.map (fun iterator -> {b with iterator}) (iterator    i) @
      List.map (fun var      -> {b with var})      (pattern_var x)

    let predicate p =
      Util.take_while (fun p' -> p <> p') all_predicates

    let parallel_bindings bs =
      (* I think preventing name collisions genuinely requires a separate
         traversal *)
      let env = Bound_vars.bindings bs in
      let rec del1_shrink1 = function
        | [] ->
            [], []
        | ({var = x; iterator = i} as b) :: bs ->
            let del, shrunk = del1_shrink1 bs in
            let cons_b (bs', subst) = b :: bs', subst in
            ( (bs, Substitution.delete x) :: List.map cons_b del
            , List.map
                (fun iterator -> {b with iterator} :: bs, Substitution.identity)
                (iterator i) @
              List.filter_map
                (fun var ->
                   if Environment.is_bound var env
                   then None
                   else Some ({b with var} :: bs,
                              if Var.equal var Var.wildcard
                              then Substitution.delete x
                              else Substitution.rename x var))
                (pattern_var x) @
              List.map cons_b shrunk )
      in
      match del1_shrink1 bs with
      | [[], _], shrunk -> shrunk
      | del,     shrunk -> del @ shrunk

    (* Shrinking-specific substitution: deleted variables become every possible
       value *)
    module Substitute = struct
      open Util.List_monad

      let list elt subst = traverse (elt subst)

      let int_term subst = function
        | Literal  n -> pure (Literal n)
        | Variable x -> match Substitution.apply subst x with
          | None              -> pure (Variable x)
          | Some Deleted      -> all_small_int_lits
          | Some (Renamed x') -> pure (Variable x')

      let iterator subst = function
        | Range { start; direction; stop } ->
          let+ start = int_term subst start
          and+ stop  = int_term subst stop in
          Range { start; direction; stop }
        | Sequence seq ->
          let+ seq = list int_term subst seq in
          Sequence seq

      let rec parallel_bindings subst = function
        | [] ->
          (pure [], Environment.empty)
        | ({var; iterator = i} as b) :: bs ->
          let bss, env = parallel_bindings subst bs in
          ( (let+ iterator = iterator subst i
             and+ bs       = bss in
             {b with iterator} :: bs)
          , Environment.add var env )

      let rec clauses subst = function
        | [] ->
          pure []
        | For bs :: cs ->
          let bss, env = parallel_bindings subst bs in
          let subst    = Substitution.shadow_env env subst in
          let+ cs = clauses subst cs
          and+ bs = bss in
          For bs :: cs
        | (When(pred, x) as c) :: cs ->
          let css = clauses subst cs in
          match Substitution.apply subst x with
          | None ->
            let+ cs = css in
            c :: cs
          | Some Deleted ->
            css
          | Some (Renamed x') ->
            let+ cs = css in
            When(pred, x') :: cs
    end

    let clauses cs =
      let rec del1_shrink1 = function
        | [] ->
            [], []
        | (For bs as c) :: cs ->
            let env = Bound_vars.bindings bs in
            let bss_substs = parallel_bindings bs in
            let del, shrunk = del1_shrink1 cs in
            let cons_c cs' = c :: cs' in
            ( Substitute.clauses (Substitution.delete_env env) cs @
              List.map cons_c del
            , (let open Util.List_monad in
               let* bs, subst = bss_substs in
               let+ cs        = Substitute.clauses subst cs in
               For bs :: cs) @
              List.map cons_c shrunk )
        | (When(pred, x) as c) :: cs ->
            (* By the time we get here, [x] is guaranteed to be in scope;
               otherwise, [Substitute.clauses] would have deleted it *)
            let del, shrunk = del1_shrink1 cs in
            let cons_c cs' = c :: cs' in
            ( cs :: List.map cons_c del
            , List.map (fun pred -> When(pred, x) :: cs) (predicate pred) @
              List.map cons_c shrunk )
      in
      match del1_shrink1 cs with
      | [[]], shrunk -> shrunk
      | del,  shrunk -> del @ shrunk

    let comprehension {env = _; clauses = cs} =
      (* I don't think there's a nice way to either (1) rule out empty lists of
         clauses ahead of time, or (2) compute the environment along the way, so
         we handle both directly via post-processing here. *)
      List.filter_map
        (fun clauses ->
           match clauses with
           | []     -> None
           | _ :: _ -> Some { env = Bound_vars.clauses clauses; clauses })
        (clauses cs)

    (* Shrinking twice simplifies both bugs this found on its first go-round,
       since this way we can shrink both the endpoints of a to/downto range or
       shrink two parallel variable names at once. *)
    let comprehension = QuickCheck.Shrink.shrink2 comprehension
  end

  module To_string = struct
    type format = OCaml_list | OCaml_array | Haskell | Python

    let surround o c s = o ^ s ^ c

    let parenthesize = surround "(" ")"
    let bracket      = surround "[" "]"
    let spaced       = surround " " " "

    let tokens          = String.concat " "
    let comma_separated = String.concat ", "

    let comprehension_clauses o = match o with
      | OCaml_list | OCaml_array | Python -> tokens
      | Haskell                           -> comma_separated

    let tuple = function
      | [tok] -> tok
      | toks  -> toks |> comma_separated |> parenthesize

    let sequence = function
      | OCaml_list | Haskell | Python -> bracket
      | OCaml_array                   -> surround "[|" "|]"

    let mod_ = function
      | OCaml_list | OCaml_array -> "mod"
      | Haskell                  -> "`mod`"
      | Python                   -> "%"

    let eq = function
      | OCaml_list | OCaml_array -> "="
      | Haskell | Python         -> "=="

    let neq = function
      | OCaml_list | OCaml_array -> "<>"
      | Haskell                  -> "/="
      | Python                   -> "!="

    let int_term = function
      | Literal  n -> Int.to_string n
      | Variable x -> x

    let succ_int_term = function
      | Literal  n -> Int.to_string (n + 1)
      | Variable x -> x ^ "+1"

    let pred_int_term = function
      | Literal  n -> Int.to_string (n - 1)
      | Variable x -> x ^ "-1"

    let modulo_check o tgt = [mod_ o; "2"; eq o; tgt]

    let predicate o = function
      | Positive -> [], [">";   "0"]
      | Negative -> [], ["<";   "0"]
      | Nonzero  -> [], [neq o; "0"]
      | Even -> begin
          match o with
          | OCaml_list | OCaml_array -> ["abs"],  modulo_check o "0"
          | Haskell                  -> ["even"], []
          | Python                   -> [],       modulo_check o "0"
        end
      | Odd -> begin
          match o with
          | OCaml_list | OCaml_array -> ["abs"], modulo_check o "1"
          | Haskell                  -> ["odd"], []
          | Python                   -> [],      modulo_check o "1"
        end

    let ocaml_direction = function
      | To     -> "to"
      | Downto -> "downto"

    let binding o {var; iterator} =
      let iter = match iterator with
        | Range {start; direction; stop} -> begin
            match o with
            | OCaml_list | OCaml_array ->
                tokens [ "="
                       ; int_term start
                       ; ocaml_direction direction
                       ; int_term stop ]
            | Haskell ->
                let step = match start, direction with
                  | _,          To     -> ""
                  | Literal  n, Downto -> "," ^ Int.to_string (n-1)
                  | Variable x, Downto -> "," ^ x ^ "-1"
                in
                let format_dotdot = match stop with
                  | Literal n when n < 0 -> spaced
                  | _                    -> Fun.id
                in
                tokens [ "<-"
                       ; "[" ^
                           int_term start ^ step ^
                           format_dotdot ".." ^
                           int_term stop ^
                         "]" ]
            | Python ->
                let stop, step = match direction with
                  | To     -> succ_int_term stop, []
                  | Downto -> pred_int_term stop, ["-1"]
                in
                "in range" ^ tuple ([int_term start; stop] @ step)
          end
        | Sequence seq ->
            let sep = match o with
              | OCaml_list | OCaml_array -> ";"
              | Haskell | Python -> ","
            in
            let seq = seq
                      |> List.map int_term
                      |> String.concat (sep ^ " ")
                      |> sequence o
            in
            let bind = match o with
              | OCaml_list | OCaml_array | Python -> "in"
              | Haskell                           -> "<-"
            in
            tokens [bind; seq]
      in
      tokens [var; iter]

    (* In Haskell and Python, parallel bindings are interpreted as sequential
       bindings.  This is fine unless (1) a variable [x] is in scope for the
       parallel bindings, (2) one of the parallel bindings binds [x] to
       something new, and (3) [x] is used on the right-hand side of a later
       binding.  In this case, Python will see the new binding of [x], which
       will shadow the old one; in OCaml, as these are all in parallel, this is
       not the case.  This function renames all such variables to [outer_x], and
       returns the python string that binds them. *)
    let protect_parallel_bindings let_clause bindings =
      let (_bound_vars, _free_vars, outer_lets), bindings =
        List.fold_left_map
          (fun (shadowed, free_vars, outer_lets) {var; iterator} ->
             let protect free_vars = function
               | Variable x when Environment.is_bound x shadowed ->
                   let outer = "outer_" ^ x in
                   let free_vars, outer_let =
                     if Environment.is_bound x free_vars
                     then free_vars,
                          None
                     else Environment.add x free_vars,
                          Some (let_clause outer x)
                   in
                   Variable outer, free_vars, outer_let
               | t ->
                   t, free_vars, None
             in
             let iterator, free_vars, outer_lets' =
               match iterator with
               | Range { start; direction; stop } ->
                   let start, free_vars, start_outer =
                     protect free_vars start
                   in
                   let stop, free_vars, stop_outer =
                     protect free_vars stop
                   in
                   let outer_lets' =
                     List.filter_map Fun.id [start_outer; stop_outer]
                   in
                   Range { start; direction; stop }, free_vars, outer_lets'
               | Sequence seq ->
                   let rev_seq, free_vars, outer_lets' =
                     List.fold_left
                       (fun (rev_ts, free_vars, outer_lets') t ->
                          let t, free_vars, outer = protect free_vars t in
                          t :: rev_ts,
                          free_vars,
                          Option.fold
                            ~none:Fun.id ~some:List.cons outer outer_lets')
                       ([], free_vars, [])
                       seq
                   in
                   Sequence (List.rev rev_seq), free_vars, outer_lets'
             in
             ( ( Environment.add var shadowed
               , free_vars
               , outer_lets' :: outer_lets )
             , {var; iterator} ))
          (Environment.empty, Environment.empty, [])
          bindings
      in
      let outer_lets =
        let rec rev_rev_concat acc = function
          | []        -> acc
          | xs :: xss -> rev_rev_concat (List.rev_append xs acc) xss
        in rev_rev_concat [] outer_lets
      in
      outer_lets, bindings

    let clause o = function
      | For bindings ->
          let intro, sep, (extra_clauses, bindings) =
            match o with
            | OCaml_list | OCaml_array ->
                ["for"], " and ", ([], bindings)
            | Haskell ->
                [],
                ", ",
                protect_parallel_bindings
                  (fun x e -> tokens ["let"; x; "="; e])
                  bindings
            | Python ->
                ["for"],
                " for ",
                protect_parallel_bindings
                  (fun x e -> tokens ["for"; x; "in"; parenthesize (e ^ ",")])
                  bindings
          in
          comprehension_clauses o
            (extra_clauses @
             intro @
             [bindings |> List.map (binding o) |> String.concat sep])
      | When(pred, x) ->
          let kwd = match o with
            | OCaml_list | OCaml_array -> ["when"]
            | Haskell                  -> []
            | Python                   -> ["if"]
          in
          let pred_pre, pred_post = predicate o pred in
          tokens (kwd @ pred_pre @ (x :: pred_post))

    let comprehension o {env; clauses} =
      let clauses = match o with
        | OCaml_list | OCaml_array -> List.rev clauses
        | Haskell | Python         -> clauses
      in
      let body    = tuple (Environment.variables env) in
      let clauses = comprehension_clauses o (List.map (clause o) clauses) in
      let sep     = match o with
        | OCaml_list | OCaml_array | Python -> " "
        | Haskell                           -> " | "
      in
      sequence o (body ^ sep ^ clauses)
  end

  let generator = Generator.comprehension
  let shrink    = Shrink.comprehension
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

  let input_haskell_list_as_python_list i =
    i |> input_line |> Str.global_replace (Str.regexp ",") ", "

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

  (* If GHCi isn't on a tty, it doesn't display a prompt, AFAICT *)
  let haskell ~f =
    command
      "/usr/bin/ghci"
      ["-v0"; "-ignore-dot-ghci"]
      ~setup:(Fun.const ())
      ~input:input_haskell_list_as_python_list
      ~output:Fun.id
      ~f
end

module Main = struct
  type output = { ocaml_list  : string
                ; ocaml_array : string
                ; haskell     : string
                ; python      : string }

  let output_for o output =
    match (o : Comprehension.To_string.format) with
    | OCaml_list  -> output.ocaml_list
    | OCaml_array -> output.ocaml_array
    | Haskell     -> output.haskell
    | Python      -> output.python

  let test_comprehensions_agree max_tests =
    let ( = ) = String.equal in
    Interactive_command.ocaml   ~f:(fun ocaml ->
    Interactive_command.haskell ~f:(fun haskell ->
    Interactive_command.python  ~f:(fun python ->
      QuickCheck.test max_tests Comprehension.generator Comprehension.shrink
        (fun c ->
           let ocaml_list  = ocaml   (Comprehension.to_string OCaml_list  c) in
           let ocaml_array = ocaml   (Comprehension.to_string OCaml_array c) in
           let haskell     = haskell (Comprehension.to_string Haskell     c) in
           let python      = python  (Comprehension.to_string Python      c) in
           if ocaml_list  = ocaml_array &&
              ocaml_array = haskell     &&
              haskell     = python
           then OK
           else Failed_with {ocaml_list; ocaml_array; haskell; python}))))

  let main_comprehensions_agree ?(seed = Util.random_seed ()) max_tests =
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
                 Format.printf "  Exception:\n    %s\n%!"
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
        Format.printf "%s (after %s%s):\n%!" what n_tests and_k_shrinks;
        print_comprehension "OCaml list" " " OCaml_list;
        print_comprehension "OCaml array" "" OCaml_array;
        print_comprehension "Haskell" "    " Haskell;
        print_comprehension "Python" "     " Python;
        print_extra_information ()
end

let () = Main.main_comprehensions_agree 1_000
