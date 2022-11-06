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
  {a1 = (cons_r 11; {v = ((cons_r 12; v).v)});
   a2 = (cons_r 9; {v = ((cons_r 10; v).v)});
   x = (cons_r 8; x);
   v = (cons_r 6; {v = ((cons_r 7; v).v)});
   z = (cons_r 5; z);
   b1 = (cons_r 3; {v = ((cons_r 4; v).v)});
   b2 = (cons_r 1; {v = ((cons_r 2; v).v)});
  }

type bar = { x : int; z : int }

let b : bar = { x = 3; z = 42 }

let b' : baz = Obj.magic b

let b' = id1 b'

let _ = assert (List.for_all2 (=) !r [12;11;10;9;8;7;6;5;4;3;2;1])

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
|}]
