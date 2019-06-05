default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

let 'var = 32

function main() -> unit = {
  let x: bits('var) = 0xFFFF_FFFF;
  let y: bits(32) = 0xFFFF_FFFF;
  assert(x == y);
  print_endline("ok")
}
