(* TEST
  flags = "-extension comprehensions_experimental"
   * expect
*)

module type S = sig
  type t
  val x : t
end;;

let t = (module struct
  type t = int
  let x = 3
end : S);;
[%%expect {|
module type S = sig type t val x : t end
val t : (module S) = <module>
|}];;

let f () =
  [ M.x for (module M : S) in [ t ] ];;
[%%expect {|
Line 2, characters 20-21:
2 |   [ M.x for (module M : S) in [ t ] ];;
                        ^
Error: Modules are not allowed in this pattern.
|}];;

let f () =
  [ M.x
    for (module M :S) in
      [ (module struct
          type t = int
          let x = 3
         end : S)
      ]
  ];;
[%%expect {|
Line 3, characters 16-17:
3 |     for (module M :S) in
                    ^
Error: Modules are not allowed in this pattern.
|}];;
