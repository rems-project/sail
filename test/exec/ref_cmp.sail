default Order dec

$include <prelude.sail>

struct S = {
  value : bits(32)
}

register R : S

let X : vector(1, register(S)) = [ref R]

function main() -> unit = print_endline("ok")
