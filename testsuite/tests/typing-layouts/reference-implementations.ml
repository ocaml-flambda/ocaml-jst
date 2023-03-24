(* TEST
   flags = "-extension comprehensions"
   * skip
   reason = "Unboxed types aren't implemented yet"
   ** expect
*)
(* CR layouts (v2): Enable this test *)

(* Constant seed for repeatable random-testing properties *)
let () = Random.init 1234

[%%expect {|
|}]

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
success
|}]

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

  (* CR layouts (v2): Test the other functions. See TANDC-1809 *)

[%%expect {|
success
|}]

(* CR layouts (v2): Cover other types, once we're happy with the above *)
