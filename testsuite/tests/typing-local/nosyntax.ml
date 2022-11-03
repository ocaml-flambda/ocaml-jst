(* TEST
   flags += "-disable-all-extensions"
   * expect *)

type fn = string -> int
type lfn = (string[@ocaml.local]) -> int
type lfn' = local_ string -> int
[%%expect{|
type fn = string -> int
type lfn = (string [@local]) -> int
Line 3, characters 19-25:
3 | type lfn' = local_ string -> int
                       ^^^^^^
Error: The local extension is disabled
       To enable it, pass the '-extension local' flag
|}]

let cast (x : fn) = (x : lfn)
[%%expect{|
Line 1, characters 21-22:
1 | let cast (x : fn) = (x : lfn)
                         ^
Error: This expression has type fn = string -> int
       but an expression was expected of type lfn = (string [@local]) -> int
|}]

let local_ref (f : lfn -> unit) =
  f (fun s -> let _ = [|s;s;s|] in 1)

[%%expect{|
val local_ref : (lfn -> unit) -> unit = <fun>
|}]

type foo = {
  global_ x :  string
}
[%%expect{|
type foo = { global_ x : string; }
|}]
(* FIXME the above should fail *)

type foo = Foo of string
type gfoo = GFoo of (string [@ocaml.global])
type gfoo' = Gfoo of global_ string

[%%expect{|
type foo = Foo of string
type gfoo = GFoo of (string [@global])
type gfoo' = Gfoo of (string [@global])
|}]
(* FIXME: gfoo' should trigger error *)

let cast1 ((x : foo) [@ocaml.local]) = match x with
  Foo s -> GFoo s
[%%expect{|
Line 2, characters 16-17:
2 |   Foo s -> GFoo s
                    ^
Error: This value escapes its region
|}]



