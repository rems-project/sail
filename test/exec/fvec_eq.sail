default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

val main : unit -> unit

function main() = {
  let x = [0x00, 0xFF, 0xAA];
  let y = [0x00, 0xFF, 0xAA];
  assert(x == y);
  print_endline("ok")
}
