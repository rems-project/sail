default Order dec
$include <prelude.sail>

val "print_endline" : string -> unit

function main() -> unit = {
  let x = bitzero;
  let y = bitone;
  let z = bitzero;
  let bv = [x, y, z];
  assert(bv == 0b010);
  print_endline("ok")
}