(* TEST
   flags += "-extension unique"
 * native
   reference = "${test_source_directory}/unique_sort.reference"
*)

type list_tag = private List
type unit2_tag = private Unit2
type chain_tag = private Chain
type buckets_tag = private Buckets

type ('a, 'hd, 'tl, 'kind) tag =
  | Cons : ('a, 'a, 'a list, list_tag) tag
  | Unit2 : ('a, unit, unit, unit2_tag) tag
  | Chain : ('a, 'a, 'a chain, chain_tag) tag
  | ChainEnd : ('a, 'a, 'a, chain_tag) tag
  | Link : ('a, 'a chain, 'a buckets, buckets_tag) tag
  | LinkSingle : ('a, 'a, 'a buckets, buckets_tag) tag

and ('a, 'kind) t =
  | Node : { tag : ('a, 'hd, 'tl, 'kind) tag; hd : 'hd; tl : 'tl } -> ('a, 'kind) t
  | Nil : ('a, list_tag) t
  | LinkEnd : ('a, buckets_tag) t

and 'a list = ('a, list_tag) t
and unit2 = (unit, unit2_tag) t
and 'a chain = ('a, chain_tag) t
and 'a buckets = ('a, buckets_tag) t

let rec to_list : type a. unique_ a chain -> unique_ unit2 -> unique_ a list = fun c u ->
  match c with
  | Node ({ tag = Chain; hd = a; tl = cs } as c) -> Node { unique_ c with tag = Cons; tl = to_list cs u }
  | Node ({ tag = ChainEnd; tl = b } as c) ->
      match u with | Node u ->
        Node { unique_ c with tag = Cons; tl = Node { unique_ u with tag = Cons; hd = b; tl = Nil } }

let rec to_buckets : type a. unique_ a list -> unique_ a buckets = fun xs ->
  match xs with
  | Node ({ tag = Cons; tl = xx } as xs) -> Node { unique_ xs with tag = LinkSingle; tl = to_buckets xx }
  | Nil -> LinkEnd

let rec merge_last : type a. (local_ a -> local_ a -> int) -> unique_ a -> unique_ a chain -> unique_ unit2 -> unique_ a chain = fun cmp a c2 u1 ->
  match u1 with Node u1 ->
  match c2 with
  | Node ({ tag = Chain; hd = c; tl = cs2 } as c2) ->
      if cmp (borrow_ a) (borrow_ c) > 0
      then Node { unique_ c2 with tl = merge_last cmp a cs2 (Node u1) }
      else Node { unique_ u1 with tag = Chain; hd = a; tl = Node c2 }
  | Node ({ tag = ChainEnd; hd = b; tl = c } as c2) ->
      if cmp (borrow_ a) (borrow_ b) > 0
      then Node { unique_ c2 with tag = Chain; hd = b; tl =
                    if cmp (borrow_ a) (borrow_ c) > 0
                    then Node { unique_ u1 with tag = ChainEnd; hd = c; tl = a }
                    else Node { unique_ u1 with tag = ChainEnd; hd = a; tl = c } }
      else Node { unique_ c2 with tag = Chain; hd = a; tl = Node { unique_ u1 with tag = ChainEnd; hd = b; tl = c } }

let rec merge_last2 : type a. (local_ a -> local_ a -> int) -> unique_ a -> unique_ a -> unique_ a chain -> unique_ unit2 -> unique_ unit2 -> unique_ a chain = fun cmp a b c2 u1 u2 ->
  match u2 with Node u2 ->
  match c2 with
  | Node ({ tag = Chain; hd = c; tl = cs2 } as c2) ->
      if cmp (borrow_ a) (borrow_ c) > 0
      then Node { unique_ c2 with tag = Chain; hd = c; tl = merge_last2 cmp a b cs2 u1 (Node u2) }
      else Node { unique_ u2 with tag = Chain; hd = a; tl = merge_last cmp b (Node c2) u1 }
  | Node ({ tag = ChainEnd; hd = c; tl = d } as c2) ->
      match u1 with Node u1 ->
      if cmp (borrow_ a) (borrow_ c) > 0
        then Node { unique_ u1 with tag = Chain; hd = c; tl =
                      if cmp (borrow_ a) (borrow_ d) > 0
                      then Node { unique_ u2 with tag = Chain; hd = d; tl = Node { unique_ c2 with hd = a; tl = b } }
                      else Node { unique_ u2 with tag = Chain; hd = a; tl = Node { unique_ c2 with hd = b; tl = d } } }
        else Node { unique_ u1 with tag = Chain; hd = a; tl =
                      if cmp (borrow_ b) (borrow_ c) > 0
                      then Node { unique_ u2 with tag = Chain; hd = c; tl =
                                    if cmp (borrow_ b) (borrow_ d) > 0
                                    then Node { unique_ c2 with hd = d; tl = b }
                                    else Node { unique_ c2 with hd = b; tl = d } }
                      else Node { unique_ u2 with tag = Chain; hd = b; tl = Node { unique_ c2 with hd = c; tl = d } } }

let rec merge : type a. (local_ a -> local_ a -> int) -> (local_ a -> local_ a -> int) -> unique_ a chain -> unique_ a chain -> unique_ unit2 -> unique_ a chain = fun cmp cmp1 c1 c2 u ->
  match c1 with
  | Node ({ tag = ChainEnd; hd = a; tl = b } as c1) ->
      merge_last2 cmp a b c2 u (Node { unique_ c1 with tag = Unit2; hd = (); tl = () })
  | Node ({ tag = Chain; hd = a; tl = cs1 } as c1) ->
      match c2 with
      | Node ({ tag = ChainEnd; hd = b; tl = c } as c2) ->
          merge_last2 cmp1 b c (Node c1) u (Node { unique_ c2 with tag = Unit2; hd = (); tl = () })
      | Node ({ tag = Chain; hd = b; tl = cs2 } as c2) ->
          if cmp (borrow_ a) (borrow_ b) > 0
          then Node ({ unique_ c2 with tag = Chain; tl = merge cmp cmp1 (Node c1) cs2 u })
          else Node ({ unique_ c1 with tag = Chain; tl = merge cmp cmp1 cs1 (Node c2) u })

let rec merge_pairs : type a. (local_ a -> local_ a -> int) -> (local_ a -> local_ a -> int) -> unique_ a buckets -> unique_ a buckets = fun cmp cmp1 xs ->
  match xs with
  | Node ({ tag = Link; hd = a; tl = Node ({ tag = Link; hd = b; tl } as xx) } as xs) ->
      Node { unique_ xs with tag = Link; hd = merge cmp cmp1 a b (Node { unique_ xx with tag = Unit2; hd = (); tl = () }); tl = merge_pairs cmp cmp1 tl }
  | Node ({ tag = Link; hd = a; tl = Node ({ tag = LinkSingle; hd = b; tl } as xx) } as xs) ->
      Node { unique_ xs with tag = Link; hd = merge_last cmp1 b a (Node { unique_ xx with tag = Unit2; hd = (); tl = () }); tl = merge_pairs cmp cmp1 tl }
  | Node { tag = Link; tl = LinkEnd } -> xs
  | Node ({ tag = LinkSingle; hd = a; tl = Node ({ tag = Link; hd = b; tl } as xx) } as xs) ->
      Node { unique_ xs with tag = Link; hd = merge_last cmp a b (Node { unique_ xx with tag = Unit2; hd = (); tl = () }); tl = merge_pairs cmp cmp1 tl }
  | Node ({ tag = LinkSingle; hd = a; tl = Node ({ tag = LinkSingle; hd = b; tl } as xx) } as xs) ->
      Node { unique_ xs with tag = Link;
                             hd = if cmp (borrow_ a) (borrow_ b) > 0
                               then Node { unique_ xx with tag = ChainEnd; hd = b; tl = a }
                               else Node { unique_ xx with tag = ChainEnd; hd = a; tl = b };
                             tl = merge_pairs cmp cmp1 tl }
  | Node { tag = LinkSingle; tl = LinkEnd } -> xs
  | LinkEnd -> xs

let rec merge_all : type a. (local_ a -> local_ a -> int) -> (local_ a -> local_ a -> int) -> unique_ a buckets -> unique_ a list = fun cmp cmp1 xs ->
  match xs with
  | Node ({ tag = Link; hd; tl = LinkEnd } as xs) -> to_list hd (Node { unique_ xs with tag = Unit2; hd = (); tl = () })
  | Node ({ tag = LinkSingle; tl = LinkEnd } as xs) -> Node { unique_ xs with tag = Cons; tl = Nil }
  | _ -> merge_all cmp cmp1 (merge_pairs cmp cmp1 xs)

(* To make this more performant, we could use the Haskell trick of turning ascending or descending sequences
   in the original list into their own chains at the start of the algorithm. This Koka code shows how to do it
   with the reuse implicit. *)

(* fun sequences(xs : list<elem>) : <div> bucket<elem> *)
(*      match(xs) *)
(*          Cons(a, Cons(b, xs1)) *)
(*              if(a > b) then descending(b, ChainEnd(b, a), xs1, Unit2((), *)
(* ())) *)
(*              else ascending(b, ChainEnd(b, a), xs1, Unit2((), ())) *)
(*          Cons(a, Nil) -> LinkSingle(a, LinkEnd) *)
(*          Nil -> LinkEnd *)

(* fun descending(a : elem, chain : chain<elem>, bs : list<elem>, u : *)
(* unit2) : <div> bucket<elem> *)
(*      match(bs) *)
(*          Cons(b, bs1) | a > b -> descending(b, Chain(b, chain), bs1, u) *)
(*          _ -> Link(chain, sequences(bs)) *)

(* fun ascending(a : elem, chain : chain<elem>, bs : list<elem>, u : unit2) *)
(* : <div> bucket<elem> *)
(*      match(bs) *)
(*          Cons(b, bs1) | (a <= b) -> ascending(b, Chain(b, chain), bs1, u) *)
(*          _ -> Link(reverse-chain(chain), sequences(bs)) *)

(*
let reverse_chain : type a. unique_ a chain -> unique_ a chain = fun c ->
  let rec loop : type a. unique_ a chain -> unique_ a chain -> unique_ a unit2 -> unique_ a chain = fun c acc u ->
      match c with
      | Node ({ tag = Chain; tl = cs } as c) -> loop cs (Node { unique_ c with tl = acc }) u
      | Node ({ tag = ChainEnd; hd = a; tl = b } as c) ->
          match u with | Node u ->
            Node { unique_ u with tag = Chain; hd = b; tl = Node { unique_ c with tag = Chain; hd = a; tl = acc } }
  in match c with
  | Node ({ tag = Chain; hd = a; tl = Node ({ tag = Chain; hd = b; tl = cs } as c' )} as c) ->
      loop cs (Node { unique_ c' with tag = ChainEnd; hd = b; tl = a }) (Node { unique_ c with tag = Unit2; hd = (); tl = () })
  | Node ({ tag = Chain; hd = a; tl = Node ({ tag = ChainEnd; hd = b; tl = c'' } as c' )} as c) ->
      Node { unique_ c' with tag = Chain; hd = c''; tl = Node { unique_ c with tag = ChainEnd; hd = b; tl = a } }
  | Node ({ tag = ChainEnd; hd = a; tl = b } as c) -> Node { unique_ c with hd = b; tl = a }
*)

let () =
  let _xs = Node { tag = Cons; hd = 2; tl = Node { tag = Cons; hd = 3; tl = Node { tag = Cons; hd = 1; tl = Nil } } } in
  let _cmp x y = x - y in
  let _cmp1 x y = x - y + 1 in
  (* cmp1 a b > 0 iff cmp a b >= 0
     We switch between these functions to get a stable merge-sort *)

  let prebefore = Gc.allocated_bytes () in
  let before = Gc.allocated_bytes () in
  (* let _ = Sys.opaque_identity (merge_all cmp cmp1 (to_buckets xs)) in *)
  let _ = Sys.opaque_identity () in
  let after = Gc.allocated_bytes () in
  let delta =
    int_of_float ((after -. before) -. (before -. prebefore))
    / (Sys.word_size/8)
  in
  let msg =
    match delta with
    | 0 -> "No Allocation"
    | n -> "Allocation"
  in
  Printf.printf "%15s: %s\n" "List.sort" msg
