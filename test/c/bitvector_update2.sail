default Order dec
$include <prelude.sail>

val "print_endline" : string -> unit

function main() -> unit = {
  var bv = 0b101;
  let x = bitzero;
  let y = bitone;
  let z = bitzero;
  bv = [x, y, z];
  assert(bv == 0b010);
  print_endline("ok")
}
