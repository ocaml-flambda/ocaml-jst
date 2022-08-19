(* TEST
  flags = "-extension Comprehensions"
   * expect
*)

(*******************************************************************************
 * Tests for special array comprehension behavior that don't have a direct
 * analog for lists
 ******************************************************************************)

let ( >> ) = Int.shift_right;;

(* We pre-allocate the resulting array if it has a statically-knowable size,
   which we can see by including 0 in something that would otherwise run for
   close enough to forever. *)

(* CR aspectorzabusky: Something is wrong here *)

(* [|i,j,k for i = 1 to 0 and j = 0 to Int.max_int/1024 and k = 0 downto Int.min_int >> 8|];;
 * [%%expect{|
 * Line 1, characters 82-84:
 * 1 | [|i,j,k for i = 1 to 0 and j = 0 to Int.max_int/1024 and k = 0 downto Int.min_int >> 8|];;
 *                                                                                       ^^
 * Error: Unbound value >>
 * |}];;
 *
 * [|i,j,k for i = 0 to Int.max_int/1024 and j = 1 to 0 and k = 0 downto Int.min_int >> 8|];;
 * [%%expect{|
 * Line 1, characters 82-84:
 * 1 | [|i,j,k for i = 0 to Int.max_int/1024 and j = 1 to 0 and k = 0 downto Int.min_int >> 8|];;
 *                                                                                       ^^
 * Error: Unbound value >>
 * |}];;
 *
 * [|i,j,k for i = 0 to Int.max_int/1024 and j = 0 downto Int.min_int >> 8 and k = 1 to 0|];;
 * [%%expect{|
 * Line 1, characters 67-69:
 * 1 | [|i,j,k for i = 0 to Int.max_int/1024 and j = 0 downto Int.min_int >> 8 and k = 1 to 0|];;
 *                                                                        ^^
 * Error: Unbound value >>
 * |}];; *)



[%%expect{|
val ( >> ) : int -> int -> int = <fun>
|}]
