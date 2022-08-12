type _ foo =
  | Ifoo : int foo
  | Ufoo : unit foo

let generate_value (type a) (foo : a foo) =
  match foo with
  | Ifoo -> (), (42 : a)
  | Ufoo -> (), ()




module M = struct
  type a
end

let foo (type b [@immediate]) (a : M.a) (eq : (M.a,b) eq) =
  match eq with
  | Refl -> use_immediate a
