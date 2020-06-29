default Order dec

$include <prelude.sail>

struct foo = {
  a : int,
  b : int
}

let foo_val : foo = struct {
  a = 1
}
