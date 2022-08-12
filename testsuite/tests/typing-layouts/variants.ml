type foo = Foo

let foo f =
 match f with
 | Foo -> 42

type 'a bar = Bar : int -> int bar
            | Baz : 'a -> 'a  bar

let bar b =
  match b with
  | Bar a -> a
  | Baz _ -> 42
