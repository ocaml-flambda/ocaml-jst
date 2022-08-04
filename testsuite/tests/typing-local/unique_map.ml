(* TEST
 * expect *)

type 'a list =
  | Cons of { hd : 'a; tl : 'a list }
  | Nil
[%%expect{|
type 'a list = Cons of { hd : 'a; tl : 'a list; } | Nil
|}]

let rec map f (unique_ xs) =
  match xs with
  | Nil -> xs
  | Cons ({hd;tl} as xs) -> Cons { unique_ xs with hd = f hd; tl = map f tl }
[%%expect{|
>> Fatal error: Bytegen.comp_primitive
Uncaught exception: Misc.Fatal_error

|}]

let test = Cons { hd = 1; tl = Cons { hd = 2; tl = Cons { hd = 3; tl = Nil } } }
[%%expect{|
val test : int list =
  Cons {hd = 1; tl = Cons {hd = 2; tl = Cons {hd = 3; tl = Nil}}}
|}]

let test2 = map (fun x -> x + 1)
    (Cons { hd = 1; tl = Cons { hd = 2; tl = Cons { hd = 3; tl = Nil } } })
[%%expect{|
Line 1, characters 12-15:
1 | let test2 = map (fun x -> x + 1)
                ^^^
Error: Unbound value map
Hint: Did you mean max?
|}]
