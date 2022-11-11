(* TEST
   * expect
*)
(* CR ccasinghino: when we add the ability to make actual void types, eliminate the uses
   of Obj.magic from this file *)

type t_void [@@void]

type void_rec = { v : t_void } [@@unboxed];;
[%%expect{|
type t_void [@@void]
type void_rec = { v : t_void; } [@@unboxed]
|}]

(* Test 1: Evaluation order of records with voids *)
type baz = { a1 : void_rec;
             a2 : void_rec;
             x : int;
             v : void_rec;
             z : int;
             b1 : void_rec;
             b2 : void_rec}

let r = ref []

let cons_r x = r := x :: !r

let id1 {a1; a2; x; v; z; b1; b2} =
  {a1 = (cons_r 11; {v = ((cons_r 12; a1).v)});
   a2 = (cons_r 9; {v = ((cons_r 10; a2).v)});
   x = (cons_r 8; x);
   v = (cons_r 6; {v = ((cons_r 7; v).v)});
   z = (cons_r 5; z);
   b1 = (cons_r 3; {v = ((cons_r 4; b1).v)});
   b2 = (cons_r 1; {v = ((cons_r 2; b2).v)});
  }

type bar = { x' : int; z' : int }

let b : bar = { x' = 3; z' = 42 }

let b' : baz = Obj.magic b

let b' = id1 b'

let _ = assert (List.for_all2 (=) !r [12;11;10;9;8;7;6;5;4;3;2;1]);;

[%%expect{|
type baz = {
  a1 : void_rec;
  a2 : void_rec;
  x : int;
  v : void_rec;
  z : int;
  b1 : void_rec;
  b2 : void_rec;
}
val r : '_weak1 list ref = {contents = []}
val cons_r : '_weak1 -> unit = <fun>
val id1 : baz -> baz = <fun>
type bar = { x' : int; z' : int; }
val b : bar = {x' = 3; z' = 42}
val b' : baz =
  {a1 = <void>; a2 = <void>; x = 3; v = <void>; z = 42; b1 = <void>;
   b2 = <void>}
val b' : baz =
  {a1 = <void>; a2 = <void>; x = 3; v = <void>; z = 42; b1 = <void>;
   b2 = <void>}
- : unit = ()
|}];;


(* Test 2: evaluation order of variants with voids *)
type void_variant =
    A of t_void * void_rec * int * void_rec * int * void_rec * t_void
  | B of t_void
  | C of void_rec * t_void
  | D of { a1 : t_void;
           a2 : void_rec;
           x : int;
           v : void_rec;
           z : int;
           b1 : void_rec;
           b2 : t_void }

let r = ref []

let cons_r x = r := x :: !r

let id1 = function
  | A (a1, a2, x, v, z, b1, b2) ->
     A ((cons_r 10; a1),
        (cons_r 8; {v = ((cons_r 9; a2).v)}),
        (cons_r 7; x),
        (cons_r 5; {v = ((cons_r 6; v).v)}),
        (cons_r 4; z),
        (cons_r 2; {v = ((cons_r 3; b1).v)}),
        (cons_r 1; b2))
  | B v -> cons_r 1; B (cons_r 2; v)
  | C (vr,v) -> cons_r 1; C ({v = (cons_r 3; vr).v}, (cons_r 2; v))
  | D {a1; a2; x; v; z; b1; b2} ->
    D {a1 = (cons_r 10; a1);
       a2 = (cons_r 8; {v = ((cons_r 9; a2).v)});
       x = (cons_r 7; x);
       v = (cons_r 5; {v = ((cons_r 6; v).v)});
       z = (cons_r 4; z);
       b1 = (cons_r 2; {v = ((cons_r 3; b1).v)});
       b2 = (cons_r 1; b2)}

type for_magic =
  | MA of int * int
  | MB
  | MC
  | MD of { x' : int;
            z' : int }

let magic_A : void_variant = Obj.magic (MA (3,42))
let magic_A = id1 magic_A

let _ = assert (List.for_all2 (=) !r [10;9;8;7;6;5;4;3;2;1]);;

[%%expect {|
type void_variant =
    A of t_void * void_rec * int * void_rec * int * void_rec * t_void
  | B of t_void
  | C of void_rec * t_void
  | D of { a1 : t_void; a2 : void_rec; x : int; v : void_rec; z : int;
      b1 : void_rec; b2 : t_void;
    }
val r : '_weak2 list ref = {contents = []}
val cons_r : '_weak2 -> unit = <fun>
val id1 : void_variant -> void_variant = <fun>
type for_magic = MA of int * int | MB | MC | MD of { x' : int; z' : int; }
val magic_A : void_variant =
  A (<void>, <void>, 3, <void>, 42, <void>, <void>)
val magic_A : void_variant =
  A (<void>, <void>, 3, <void>, 42, <void>, <void>)
- : unit = ()
|}]

let _ = r := []
let magic_B : void_variant = Obj.magic MB
let magic_B = id1 magic_B
let _ = assert (List.for_all2 (=) !r [2;1]);;
[%%expect {|
- : unit = ()
val magic_B : void_variant = B <void>
val magic_B : void_variant = B <void>
- : unit = ()
|}];;

let _ = r := []
let magic_C : void_variant = Obj.magic MC
let magic_C = id1 magic_C
let _ = assert (List.for_all2 (=) !r [3;2;1]);;
[%%expect {|
- : unit = ()
val magic_C : void_variant = C (<void>, <void>)
val magic_C : void_variant = C (<void>, <void>)
- : unit = ()
|}];;

let _ = r := []
let magic_D : void_variant = Obj.magic (MD {x' = 3; z' = 42})
let magic_D = id1 magic_D
let _ = assert (List.for_all2 (=) !r [10;9;8;7;6;5;4;3;2;1]);;
[%%expect {|
- : unit = ()
val magic_D : void_variant =
  D
   {a1 = <void>; a2 = <void>; x = 3; v = <void>; z = 42; b1 = <void>;
    b2 = <void>}
val magic_D : void_variant =
  D
   {a1 = <void>; a2 = <void>; x = 3; v = <void>; z = 42; b1 = <void>;
    b2 = <void>}
- : unit = ()
|}];;

(* Test 3: top-level void bindings banned *)

let x : t_void = assert false;;
[%%expect {|
Line 1, characters 4-5:
1 | let x : t_void = assert false;;
        ^
Error: Top-level module bindings must have layout value, but x has layout
       void.
|}];;

module M3_1 = struct
  let x : t_void = assert false;;
end;;
[%%expect {|
Line 2, characters 6-7:
2 |   let x : t_void = assert false;;
          ^
Error: Top-level module bindings must have layout value, but x has layout
       void.
|}];;

module M3_2 = struct
  let x =
    match magic_B with
    | B v -> v
    | _ -> assert false
end;;
[%%expect {|
Line 2, characters 6-7:
2 |   let x =
          ^
Error: Top-level module bindings must have layout value, but x has layout
       void.
|}];;

module M3_3 = struct
  let {x} = b'

  let {z; v} = b'
end;;
[%%expect {|
Line 4, characters 10-11:
4 |   let {z; v} = b'
              ^
Error: Top-level module bindings must have layout value, but v has layout
       void.
|}];;

(* Test 4: local binding of void things is allowed and works sensibly *)
let () = r := []

type void_holder = V of t_void
type vh_formagic = VM
let vh : void_holder = Obj.magic VM

let local_void_bindings_1 vh =
  let V v = cons_r 1; vh in
  {a1 = {v = (cons_r 8; v)};
   a2 = {v = (cons_r 7; v)};
   x = (cons_r 6; 12);
   v = (cons_r 5; {v});
   z = (cons_r 4; 13);
   b1 = {v = (cons_r 3; v)};
   b2 = (cons_r 2; {v})}

let _ = local_void_bindings_1 vh

let _ = assert (List.for_all2 (=) !r [8;7;6;5;4;3;2;1]);;
[%%expect {|
type void_holder = V of t_void
type vh_formagic = VM
val vh : void_holder = V <void>
val local_void_bindings_1 : void_holder -> baz = <fun>
- : baz =
{a1 = <void>; a2 = <void>; x = 12; v = <void>; z = 13; b1 = <void>;
 b2 = <void>}
- : unit = ()
|}]

let local_void_bindings_2 b =
  let {z; a1; b1; x; b2} = b in
  (x, V b2.v, V b1.v, z, V a1.v)

let (x, _, vh2, z, _) = local_void_bindings_2 b'

let _ = assert (x = 3 && z = 42)
[%%expect {|
val local_void_bindings_2 :
  baz -> int * void_holder * void_holder * int * void_holder = <fun>
val x : int = 3
val vh2 : void_holder = V <void>
val z : int = 42
- : unit = ()
|}]

let () = r := []

let local_void_bindings_3 vh1 x y =
  let v1 =
    cons_r 1;
    match vh1 with
    | V v -> v
  in
  let x = cons_r 2; x + y in
  let v2 =
    cons_r 3;
    let _ =
      match {v = v1} with
      | {v} -> cons_r 4; v
    in
    match vh2 with
    | V v -> cons_r 5; v
  in
  let vr = {v = (cons_r 6; v2)} in
  let {v = v3} : void_rec = cons_r 7; vr in
  let z = cons_r 8; y + x in
  cons_r 9;
  {a1 = {v = v1};
   a2 = {v = let V v = vh in v};
   x;
   v = {v = v2};
   z = z;
   b1 = vr;
   b2 = {v = v3}}

let {x;z} = local_void_bindings_3 vh 3 42

let () =
  assert (x = 45 && z = 87)

let _ = assert (List.for_all2 (=) !r [9;8;7;6;5;4;3;2;1]);;
[%%expect{|
val local_void_bindings_3 : void_holder -> int -> int -> baz = <fun>
val x : int = 45
val z : int = 87
- : unit = ()
|}];;

(* CJC XXX add test cases for matching on void that can raise.

   e.g.,

   match raise Foo; voidthing with
   | voidpat -> ...
   | exception Foo -> ...

   have cases where we hit the void and where we don't
*)

(* CJC XXX

   write cases for top-level voids.

   we want some cases where the term has an indeterminate layout, and the signature a)
   mentions the term and specifies its layout, b) mentions the term and doesn't specify
   its layout, and c) doesn't mention the term.

   add test that top-level void is banned in stand-alone signatures.

   Also is the gross defaulting code I added previously still needed?
*)

(* CJC XXX check that we aren;t allowing

   match void1, void2, void3 with ...

   since this isn't quite a tuple *)

(* Now that we require match scrutinees to have a sort,
   are we still allowing [match assert false with ...] ? *)

