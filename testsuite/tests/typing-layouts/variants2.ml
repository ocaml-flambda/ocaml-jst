type 'a foo =
  | Foo : unit -> 'a foo

let bar :  type a . a foo -> a foo = function
  | Foo _ -> Foo ()
