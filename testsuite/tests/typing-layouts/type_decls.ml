
external ( == ) : 'a -> 'a -> bool = "%eq"

type 'a t = {v: 'a}

let[@inline never] compare_and_set r seen =
  r.v == seen
