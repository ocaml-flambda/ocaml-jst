(* TEST
   * expect
*)
(* CR ccasinghino: when we add the ability to make actual void types, eliminate the uses
   of Obj.magic from this file *)

(* Test 1: Evaluation order of records with voids *)
type t_void [@@void]

type void_rec = { v : t_void } [@@unboxed]

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

type bar = { x : int; z : int }

let b : bar = { x = 3; z = 42 }

let b' : baz = Obj.magic b

let b' = id1 b'

let _ = assert (List.for_all2 (=) !r [12;11;10;9;8;7;6;5;4;3;2;1]);;

[%%expect{|
type t_void [@@void]
type void_rec = { v : t_void; } [@@unboxed]
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
type bar = { x : int; z : int; }
val b : bar = {x = 3; z = 42}
val b' : baz =
  {a1 = <void>; a2 = <void>; x = 3; v = <void>; z = 42; b1 = <void>;
   b2 = <void>}
val b' : baz =
  {a1 = <void>; a2 = <void>; x = 3; v = <void>; z = 42; b1 = <void>;
   b2 = <void>}
- : unit = ()
|}];;


(* Test 2: evaluation order of variants with voids *)
type t_void [@@void]

type void_rec = { v : t_void } [@@unboxed]

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

type bar = { x : int; z : int }

let b : bar = { x = 3; z = 42 }

type for_magic =
  | MA of int * int
  | MB
  | MC
  | MD of { x : int;
            z : int }

let magic_A : void_variant = Obj.magic (MA (3,42))
let magic_A = id1 magic_A

let _ = assert (List.for_all2 (=) !r [10;9;8;7;6;5;4;3;2;1]);;

[%%expect {|
type t_void [@@void]
type void_rec = { v : t_void; } [@@unboxed]
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
type bar = { x : int; z : int; }
val b : bar = {x = 3; z = 42}
type for_magic = MA of int * int | MB | MC | MD of { x : int; z : int; }
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
let magic_D : void_variant = Obj.magic (MD {x = 3; z = 42})
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
