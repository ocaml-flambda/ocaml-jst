(* TEST
* skip
*)

type color = Red | Black

type ('k, 'v) tree =
  | Node of { color : color; left : ('k, 'v) tree; global_ key : 'k; global_ value : 'v; right : ('k, 'v) tree }
  | Leaf

let rec fold f b t =
  match t with
  | Node { left; key; value; right } ->
      fold f (f key value (fold f b left)) right
  | Leaf -> b

let work ~insert ~fold ~empty =
  let rec loop n t =
    if n <= 0 then t
      else loop (n - 1) (insert n (n mod 10 = 0) t) in
  let tree = loop 42000 empty in
  fold (fun _ v acc -> if v then acc + 1 else acc) 0 tree


(*************************************************************************
  Okasaki-style red-black trees
 *************************************************************************)

module Make_Okasaki(Ord : Map.OrderedType) = struct
  type 'a t = (Ord.t, 'a) tree

  let fold = fold

  (* t is black and its left child is red *)
  let balance_left t =
    match t with
    | Node t ->
        begin match t.left with
        | Node ({ left = Node ({ color = Red } as ll) } as l) ->
            Node { l with color = Red;
                          left = Node { ll with color = Black };
                          right = Node { t with color = Black; left = l.right } }
        | Node ({ right = Node ({ color = Red } as lr) } as l) ->
            Node { lr with color = Red;
                          left = Node { l with color = Black; right = lr.left };
                          right = Node { t with color = Black; left = lr.right } }
        | Node l ->
            Node { t with color = Black; left = Node { l with color = Red } }
        | Leaf -> Leaf
        end
    | Leaf -> Leaf

  (* t is black and its right child is red *)
  let balance_right t =
    match t with
    | Node t ->
        begin match t.right with
        | Node ({ right = Node ({ color = Red } as rr) } as r) ->
            Node { r with color = Red;
                          left = Node { t with color = Black; right = r.left };
                          right = Node { rr with color = Black } }
        | Node ({ left = Node ({ color = Red } as rl) } as r) ->
            Node { rl with color = Red;
                          left = Node { t with color = Black; right = rl.left };
                          right = Node { r with color = Black; left = rl.right } }
        | Node r ->
            Node { t with color = Black; right = Node { r with color = Red } }
        | Leaf -> Leaf
        end
    | Leaf -> Leaf

  let rec ins k v t =
    match t with
    | Node t -> begin
        match Ord.compare k t.key with
        | c when c < 0 -> begin
          match t.left with
          | Node { color = Red } -> balance_left (Node { t with left = ins k v t.left })
          | _ -> Node { t with left = ins k v t.left } end
        | c when c > 0 -> begin
          match t.right with
          | Node { color = Red } -> balance_right (Node { t with right = ins k v t.right })
          | _ -> Node { t with right = ins k v t.right } end
        | _ -> Node { t with value = v } (* k == t.key *) end
    | Leaf -> Node { color = Red; left = Leaf; key = k; value = v; right = Leaf }

  let set_black t =
    match t with
    | Node t -> Node { t with color = Black }
    | Leaf -> Leaf

  let insert k v t = set_black (ins k v t)
end


(*************************************************************************
   Okasaki-style red-black trees with uniqueness
 *************************************************************************)

module Make_Unique_Okasaki(Ord : Map.OrderedType) = struct
  type 'a t = (Ord.t, 'a) tree

  let fold = fold

  (* t is black and its left child is red *)
  let balance_left t =
    match t with
    | Node t ->
        begin match t.left with
        | Node ({ left = Node ({ color = Red } as ll) } as l) ->
            Node { unique_ l with color = Red;
                          left = Node { unique_ ll with color = Black };
                          right = Node { unique_ t with color = Black; left = l.right } }
        | Node ({ right = Node ({ color = Red } as lr) } as l) ->
            Node { unique_ lr with color = Red;
                          left = Node { unique_ l with color = Black; right = lr.left };
                          right = Node { unique_ t with color = Black; left = lr.right } }
        | Node l ->
            Node { unique_ t with color = Black; left = Node { unique_ l with color = Red } }
        | Leaf -> Leaf
        end
    | Leaf -> Leaf

  (* t is black and its right child is red *)
  let balance_right t =
    match t with
    | Node t ->
        begin match t.right with
        | Node ({ right = Node ({ color = Red } as rr) } as r) ->
            Node { unique_ r with color = Red;
                          left = Node { unique_ t with color = Black; right = r.left };
                          right = Node { unique_ rr with color = Black } }
        | Node ({ left = Node ({ color = Red } as rl) } as r) ->
            Node { unique_ rl with color = Red;
                          left = Node { unique_ t with color = Black; right = rl.left };
                          right = Node { unique_ r with color = Black; left = rl.right } }
        | Node r ->
            Node { unique_ t with color = Black; right = Node { unique_ r with color = Red } }
        | Leaf -> Leaf
        end
    | Leaf -> Leaf

  let rec ins k v t =
    match t with
    | Node t -> begin
        match Ord.compare k t.key with
        | c when c < 0 -> begin
          match t.left with
          | Node { color = Red } -> balance_left (Node { unique_ t with left = ins k v t.left })
          | _ -> Node { unique_ t with left = ins k v t.left } end
        | c when c > 0 -> begin
          match t.right with
          | Node { color = Red } -> balance_right (Node { unique_ t with right = ins k v t.right })
          | _ -> Node { unique_ t with right = ins k v t.right } end
        | _ -> Node { unique_ t with value = v } (* k == t.key *) end
    | Leaf -> Node { color = Red; left = Leaf; key = k; value = v; right = Leaf }

  let set_black t =
    match t with
    | Node t -> Node { unique_ t with color = Black }
    | Leaf -> Leaf

  let insert k v t = set_black (ins k v t)
end


(*************************************************************************
   Tree with explicit tags
 *************************************************************************)

type tree_tag = private Tree
type zipper_tag = private Zipper

type ('left, 'right, 'kind) tag =
  | Red : (tree_tag, tree_tag, tree_tag) tag
  | Black : (tree_tag, tree_tag, tree_tag) tag
  | Right_red : (tree_tag, zipper_tag, zipper_tag) tag
  | Right_black : (tree_tag, zipper_tag, zipper_tag) tag
  | Left_red : (zipper_tag, tree_tag, zipper_tag) tag
  | Left_black : (zipper_tag, tree_tag, zipper_tag) tag

type ('k, 'v, 'kind) tagged_tree =
  | Node : { color : ('left, 'right, 'kind) tag;
             left : ('k, 'v, 'left) tagged_tree;
             global_ key : 'k;
             global_ value : 'v;
             right : ('k, 'v, 'right) tagged_tree }
      -> ('k, 'v, 'kind) tagged_tree
  | Leaf : ('k, 'v, 'kind) tagged_tree

let rec tagged_fold : 'k 'v 'kind 'a. ('k -> 'v -> 'a -> 'a) -> 'a -> ('k, 'v, 'kind) tagged_tree -> 'a = fun f a t ->
  match t with
  | Node { left; key; value; right } ->
      tagged_fold f (f key value (tagged_fold f a left)) right
  | Leaf -> a

let unique_work ~insert ~fold ~empty =
  let rec loop n (unique_ t) =
    if n <= 0 then t
    else loop (n - 1) (insert n (n mod 10 = 0) t) in
  let unique_ tree = loop 42000 empty in
  fold (fun _ v acc -> if v then acc + 1 else acc) 0 tree


(*************************************************************************
   Okasaki-style red-black trees with uniqueness and explicit tags
 *************************************************************************)

module Make_Tagged_Okasaki(Ord : Map.OrderedType) = struct
  type 'a t = (Ord.t, 'a, tree_tag) tagged_tree

  let fold = tagged_fold

  (* t is black and its left child is red *)
  let balance_left t =
    match t with
    | Node ({ color = Black } as t) ->
        begin match t.left with
        | Node ({ color = Red; left = Node ({ color = Red } as ll) } as l) ->
            Node { unique_ l with color = Red;
                          left = Node { unique_ ll with color = Black };
                          right = Node { unique_ t with color = Black; left = l.right } }
        | Node ({ color = Red; right = Node ({ color = Red } as lr) } as l) ->
            Node { unique_ lr with color = Red;
                          left = Node { unique_ l with color = Black; right = lr.left };
                          right = Node { unique_ t with color = Black; left = lr.right } }
        | Node ({ color = Red } as l) ->
            Node { unique_ t with color = Black; left = Node { unique_ l with color = Red } }
        | Node { color = Black } -> assert false
        | Leaf -> Leaf
        end
    | Node { color = Red } -> assert false
    | Leaf -> Leaf

  (* t is black and its right child is red *)
  let balance_right t =
    match t with
    | Node ({ color = Black } as t) ->
        begin match t.right with
        | Node ({ color = Red; right = Node ({ color = Red } as rr) } as r) ->
            Node { unique_ r with color = Red;
                          left = Node { unique_ t with color = Black; right = r.left };
                          right = Node { unique_ rr with color = Black } }
        | Node ({ color = Red; left = Node ({ color = Red } as rl) } as r) ->
            Node { unique_ rl with color = Red;
                          left = Node { unique_ t with color = Black; right = rl.left };
                          right = Node { unique_ r with color = Black; left = rl.right } }
        | Node ({ color = Red } as r) ->
            Node { unique_ t with color = Black; right = Node { unique_ r with color = Red } }
        | Node { color = Black } -> assert false
        | Leaf -> Leaf
        end
    | Node { color = Red } -> assert false
    | Leaf -> Leaf

  let rec ins : 'a. Ord.t -> 'a -> unique_ 'a t -> unique_ 'a t = fun k v t ->
    match t with
    | Node ({ color = Black } as t) -> begin
        match Ord.compare k t.key with
        | c when c < 0 -> begin
          match t.left with
          | Node { color = Red } -> balance_left (Node { unique_ t with left = ins k v t.left })
          | _ -> Node { unique_ t with left = ins k v t.left } end
        | c when c > 0 -> begin
          match t.right with
          | Node { color = Red } -> balance_right (Node { unique_ t with right = ins k v t.right })
          | _ -> Node { unique_ t with right = ins k v t.right } end
        | _ -> Node { unique_ t with value = v } (* k == t.key *) end
    | Node ({ color = Red } as t) -> begin (* exactly as Black case; copied due to GADT inference *)
        match Ord.compare k t.key with
        | c when c < 0 -> begin
            match t.left with
            | Node { color = Red } -> balance_left (Node { unique_ t with left = ins k v t.left })
            | _ -> Node { unique_ t with left = ins k v t.left } end
        | c when c > 0 -> begin
            match t.right with
            | Node { color = Red } -> balance_right (Node { unique_ t with right = ins k v t.right })
            | _ -> Node { unique_ t with right = ins k v t.right } end
        | _ -> Node { unique_ t with value = v } (* k == t.key *) end
    | Leaf -> Node { color = Red; left = Leaf; key = k; value = v; right = Leaf }

  let set_black t =
    match t with
    | Node ({ color = Red } as t) -> Node { unique_ t with color = Black }
    | _ -> t

  let insert k v t = set_black (ins k v t)
end


(*************************************************************************
   Bottom-up red-black trees
 *************************************************************************)

module Make_Tagged_Bottom_Up(Ord : Map.OrderedType) = struct
  type 'a t = (Ord.t, 'a, tree_tag) tagged_tree
  type 'a z = (Ord.t, 'a, zipper_tag) tagged_tree

  let fold = tagged_fold

  let rec move_up : 'a. unique_ 'a z -> unique_ 'a t -> unique_ 'a t = fun z t ->
    match z with
    | Node ({ color = Left_red; left = z' } as z) ->
        move_up z' (Node { unique_ z with color = Red; left = t })
    | Node ({ color = Left_black; left = z' } as z) ->
        move_up z' (Node { unique_ z with color = Black; left = t })
    | Node ({ color = Right_red; right = z' } as z) ->
        move_up z' (Node { unique_ z with color = Red; right = t })
    | Node ({ color = Right_black; right = z' } as z) ->
        move_up z' (Node { unique_ z with color = Black; right = t })
    | Leaf -> t

  let rec fixup : 'a. unique_ 'a z -> unique_ 'a t -> unique_ 'a t = fun z t ->
    match z with
    | Node ({ color = Left_red; left = z' } as z) -> begin
        match z' with
        | Node ({ color = Left_black; left = z''; right = y } as z') -> begin
            match y with
            | Node ({ color = Red } as y) ->
                fixup z'' (Node { unique_ z' with color = Red;
                                                  left = Node { unique_ z with color = Black; left = t };
                                                  right = Node { unique_ y with color = Black } })
            | Node { color = Black } | Leaf ->
                move_up z'' (Node { unique_ z with color = Black;
                                                   right = Node { unique_ z' with color = Red; left = z.right };
                                                   left = t }) end
        | Node ({ color = Right_black; right = z''; left = y } as z') -> begin
            match y with
            | Node ({ color = Red } as y) ->
                fixup z'' (Node { unique_ z' with color = Red;
                                                  right = Node { unique_ z with color = Black; left = t };
                                                  left = Node { unique_ y with color = Black } })
            | Node { color = Black } | Leaf ->
                match t with
                | Node ({ color = Red; left = tl; right = tr } as t) ->
                    move_up z'' (Node { unique_ t with color = Black;
                                                       left = Node { unique_ z' with color = Red; right = tl };
                                                       right = Node { unique_ z with color = Red; left = tr } })
                 | _ -> assert false end
        | _ -> assert false end
    | Node ({ color = Right_red; right = z' } as z) -> begin
        match z' with
        | Node ({ color = Right_black; right = z''; left = y } as z') -> begin
            match y with
            | Node ({ color = Red } as y) ->
                fixup z'' (Node { unique_ z' with color = Red;
                                                  right = Node { unique_ z with color = Black; right = t };
                                                  left = Node { unique_ y with color = Black } })
            | Node { color = Black } | Leaf ->
                move_up z'' (Node { unique_ z with color = Black;
                                                   left = Node { unique_ z' with color = Red; right = z.left };
                                                   right = t }) end
        | Node ({ color = Left_black; left = z''; right = y } as z') -> begin
            match y with
            | Node ({ color = Red } as y) ->
                fixup z'' (Node { unique_ z' with color = Red;
                                                  left = Node { unique_ z with color = Black; right = t };
                                                  right = Node { unique_ y with color = Black } })
            | Node { color = Black } | Leaf ->
                match t with
                | Node ({ color = Red; left = tl; right = tr } as t) ->
                    move_up z'' (Node { unique_ t with color = Black;
                                                       right = Node { unique_ z' with color = Red; left = tl };
                                                       left = Node { unique_ z with color = Red; right = tr } })
                 | _ -> assert false end
        | _ -> assert false end
    | _ -> move_up z t

  let rec ins : 'a. Ord.t -> 'a -> unique_ 'a z -> unique_ 'a t -> unique_ 'a t = fun k v z t ->
    match t with
    | Node ({ color = Black } as t) -> begin
        match Ord.compare k t.key with
        | c when c < 0 -> ins k v (Node { unique_ t with color = Left_black; left = z }) t.left
        | c when c > 0 -> ins k v (Node { unique_ t with color = Right_black; right = z }) t.right
        | _ -> move_up z (Node { unique_ t with value = v }) (* k == t.key *) end
    | Node ({ color = Red } as t) -> begin
        match Ord.compare k t.key with
        | c when c < 0 -> ins k v (Node { unique_ t with color = Left_red; left = z }) t.left
        | c when c > 0 -> ins k v (Node { unique_ t with color = Right_red; right = z }) t.right
        | _ -> move_up z (Node { unique_ t with value = v }) (* k == t.key *) end
    | Leaf -> fixup z (Node { color = Red; left = Leaf; key = k; value = v; right = Leaf })

  let set_black t =
    match t with
    | Node ({ color = Red } as t) -> Node { unique_ t with color = Black }
    | _ -> t

  let insert k v t = set_black (ins k v Leaf t)
end

module IntOrder = struct
  type t = int

  let compare t1 t2 = t1 - t2
end

let () =
  let module Ord = IntOrder in
  let module M1 = Make_Okasaki(Ord) in
  let module M2 = Make_Unique_Okasaki(Ord) in
  let module M3 = Make_Tagged_Okasaki(Ord) in
  let module M4 = Make_Tagged_Bottom_Up(Ord) in
  Printf.printf "%d\n" (work ~insert:M1.insert ~fold ~empty:Leaf);
  Printf.printf "%d\n" (unique_work ~insert:M2.insert ~fold ~empty:Leaf);
  Printf.printf "%d\n" (unique_work ~insert:M3.insert ~fold:tagged_fold ~empty:Leaf);
  Printf.printf "%d\n" (unique_work ~insert:M4.insert ~fold:tagged_fold ~empty:Leaf);
