(* TEST
   flags = "-extension comprehensions"
   * expect
*)

let () = Random.init 1234

[%%expect {|
|}]

(* we don't have collections yet, so this has to be  *)
(* CR reisenberg: Rewrite these to use collections, after v4 or v5 *)

type check_result = { passed : bool; actual : int64; expected : int64 }
type property = int64 -> check_result

let int64s = [0L; 1L; -1L; 2L; -2L; Int64.max_int; Int64.min_int] @
             List.init 20 (fun _ -> Random.bits64 ())

let int64ss = [ x, y for x in int64s and y in int64s ]

let test_nullary name prop =
  if not prop.passed
  then Printf.printf "Test failed: %s. Expected = %Li; actual = %Li\n"
       name prop.expected prop.actual

let test_unary name prop =
  let test1 x =
    let result = prop x in
    if not result.passed
    then Printf.printf "Test failed: %s. Input = %Li; expected = %Li; actual = %Li\n"
           name x result.expected result.actual
  in
  List.iter test1 int64s

let test_binary name prop =
  let test1 (x, y) =
    let result = prop x y in
    if not result.passed
    then Printf.printf "Test failed: %s. Input = %Li,%Li; expected = %Li; actual = %Li\n"
           name x y result.expected result.actual
  in
  List.iter test1 int64ss

let mk0 expected u_actual =
  let actual = Uint64.to_int64 u_actual in
  { passed = Int64.equal expected actual; expected; actual }

let mk1 expected_f actual_f arg =
  let expected = expected_f arg in
  let actual = Uint64.to_int64 (actual_f (Uint64.of_int64 arg)) in
  { passed = Int64.equal expected actual; expected; actual }

let mk2 expected_f actual_f arg1 arg2 =
  let expected = expected_f arg1 arg2 in
  let actual = Uint64.to_int64 (actual_f (Uint64.of_int64 arg1) (Uint64.of_int64 arg2)) in
  { passed = Int64.equal expected actual; expected; actual }

[%%expect {|
type check_result = { passed : bool; actual : int64; expected : int64; }
type property = int64 -> check_result
val int64s : Int64.t list =
  [0L; 1L; -1L; 2L; -2L; 9223372036854775807L; -9223372036854775808L;
   6701324795762726672L; 5282539069741454584L; 6377495809316136332L;
   -9078606286652893137L; 3883234250089591934L; 3151853085971076713L;
   1910503753774450425L; -394673393823179810L; -4096697634122379074L;
   -7326580180585313387L; -2793598017506307569L; 4189159150259432349L;
   -895777199442989164L; -4966611112974434798L; -4247517925181399784L;
   -2050657296186128033L; -6969475624567325808L; 4184538450390123947L;
   -6439732929884115256L; -2584939278118910801L]
val int64ss : (Int64.t * Int64.t) list =
  [(0L, 0L); (1L, 0L); (-1L, 0L); (2L, 0L); (-2L, 0L);
   (9223372036854775807L, 0L); (-9223372036854775808L, 0L);
   (6701324795762726672L, 0L); (5282539069741454584L, 0L);
   (6377495809316136332L, 0L); (-9078606286652893137L, 0L);
   (3883234250089591934L, 0L); (3151853085971076713L, 0L);
   (1910503753774450425L, 0L); (-394673393823179810L, 0L);
   (-4096697634122379074L, 0L); (-7326580180585313387L, 0L);
   (-2793598017506307569L, 0L); (4189159150259432349L, 0L);
   (-895777199442989164L, 0L); (-4966611112974434798L, 0L);
   (-4247517925181399784L, 0L); (-2050657296186128033L, 0L);
   (-6969475624567325808L, 0L); (4184538450390123947L, 0L);
   (-6439732929884115256L, 0L); (-2584939278118910801L, 0L); (0L, 1L);
   (1L, 1L); (-1L, 1L); (2L, 1L); (-2L, 1L); (9223372036854775807L, 1L);
   (-9223372036854775808L, 1L); (6701324795762726672L, 1L);
   (5282539069741454584L, 1L); (6377495809316136332L, 1L);
   (-9078606286652893137L, 1L); (3883234250089591934L, 1L);
   (3151853085971076713L, 1L); (1910503753774450425L, 1L);
   (-394673393823179810L, 1L); (-4096697634122379074L, 1L);
   (-7326580180585313387L, 1L); (-2793598017506307569L, 1L);
   (4189159150259432349L, 1L); (-895777199442989164L, 1L);
   (-4966611112974434798L, 1L); (-4247517925181399784L, 1L);
   (-2050657296186128033L, 1L); (-6969475624567325808L, 1L);
   (4184538450390123947L, 1L); (-6439732929884115256L, 1L);
   (-2584939278118910801L, 1L); (0L, -1L); (1L, -1L); (-1L, -1L); (2L, -1L);
   (-2L, -1L); (9223372036854775807L, -1L); (-9223372036854775808L, -1L);
   (6701324795762726672L, -1L); (5282539069741454584L, -1L);
   (6377495809316136332L, -1L); (-9078606286652893137L, -1L);
   (3883234250089591934L, -1L); (3151853085971076713L, -1L);
   (1910503753774450425L, -1L); (-394673393823179810L, -1L);
   (-4096697634122379074L, -1L); (-7326580180585313387L, -1L);
   (-2793598017506307569L, -1L); (4189159150259432349L, -1L);
   (-895777199442989164L, -1L); (-4966611112974434798L, -1L);
   (-4247517925181399784L, -1L); (-2050657296186128033L, -1L);
   (-6969475624567325808L, -1L); (4184538450390123947L, -1L);
   (-6439732929884115256L, -1L); (-2584939278118910801L, -1L); (0L, 2L);
   (1L, 2L); (-1L, 2L); (2L, 2L); (-2L, 2L); (9223372036854775807L, 2L);
   (-9223372036854775808L, 2L); (6701324795762726672L, 2L);
   (5282539069741454584L, 2L); (6377495809316136332L, 2L);
   (-9078606286652893137L, 2L); (3883234250089591934L, 2L);
   (3151853085971076713L, 2L); (1910503753774450425L, 2L);
   (-394673393823179810L, 2L); (-4096697634122379074L, 2L);
   (-7326580180585313387L, 2L); (-2793598017506307569L, 2L);
   (4189159150259432349L, ...); ...]
val test_nullary : string -> check_result -> unit = <fun>
val test_unary : string -> (Int64.t -> check_result) -> unit = <fun>
val test_binary : string -> (Int64.t -> Int64.t -> check_result) -> unit =
  <fun>
Line 33, characters 15-30:
33 |   let actual = Uint64.to_int64 u_actual in
                    ^^^^^^^^^^^^^^^
Error: Unbound module Uint64
Hint: Did you mean Int64?
|}]
(* CR reisenberg: there should be no errors above *)

let () =
  test_binary "+" (mk2 Int64.add Uint64.(+));
  test_binary "-" (mk2 Int64.sub Uint64.(-));
  test_binary "*" (mk2 Int64.mul Uint64.( * ));
  test_binary "/" (mk2 Int64.div Uint64.(/));
  test_binary "mod" (mk2 Int64.rem Uint64.(mod));
  test_unary "~-" (mk1 Int64.neg Uint64.(~-));
  test_nullary "zero" (mk0 Int64.zero Uint64.zero);
  test_nullary "one" (mk0 Int64.one Uint64.one);
  test_nullary "minus_one" (mk0 Int64.minus_one Uint64.minus_one);
  test_unary "neg" (mk1 Int64.neg Uint64.neg);
  test_binary "add" (mk2 Int64.add Uint64.add);
  test_binary "sub" (mk2 Int64.sub Uint64.sub);
  test_binary "mul" (mk2 Int64.mul Uint64.mul);
  test_binary "div" (mk2 Int64.div Uint64.div);
  test_binary "unsigned_div" (mk2 Int64.unsigned_div Uint64.unsigned_div);
  test_binary "rem" (mk2 Int64.rem Uint64.rem);
  test_binary "unsigned_rem" (mk2 Int64.unsigned_rem Uint64.unsigned_rem);
  test_unary "succ" (mk1 Int64.succ Uint64.succ);
  test_unary "pred" (mk1 Int64.pred Uint64.pred);
  test_unary "abs" (mk1 Int64.abs Uint64.abs);
  test_nullary "max_int" (mk0 Int64.max_int Uint64.max_int);
  test_nullary "min_int" (mk0 Int64.min_int Uint64.min_int);
  test_binary "logand" (mk2 Int64.logand Uint64.logand);
  test_binary "logor" (mk2 Int64.logor Uint64.logor);
  test_binary "logxor" (mk2 Int64.logxor Uint64.logxor);
  test_unary "lognot" (mk2 Int64.lognot Uint64.lognot);
  test_binary "add" (mk2 Int64.add Uint64.add);
  test_binary "add" (mk2 Int64.add Uint64.add);
  test_binary "add" (mk2 Int64.add Uint64.add);
  (* testing the rest of the functions is somewhat annoying, because the
     types vary. I'm tempted to come up with a general approach here, but
     I'm not convinced that's the best use of time.
   *)

[%%expect {|
Line 2, characters 19-22:
2 |   test_binary "+" (mk2 Int64.add Uint64.(+));
                       ^^^
Error: Unbound value mk2
|}]
(* CR reisenberg: there should be no errors above *)

(* RAE XXX repeat the above for #float, #int32, and #nativeint after feedback *)
