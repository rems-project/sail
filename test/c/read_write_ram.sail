default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>
$include <string.sail>
$include <exception_basic.sail>

val write_ram = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit effect {wmem}

val read_ram = "read_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

val main : unit -> unit effect {escape, wmem, rmem}

function main() = {
  write_ram(64, 4, 64^0x0, 64^0x8000_0000, 0x01020304);
  let data = read_ram(64, 4, 64^0x0, 64^0x8000_0000);
  assert(data == 0x01020304);
  let data = read_ram(64, 3, 64^0x0, 64^0x8000_0001);
  assert(data == 0x010203);
  let data = read_ram(64, 3, 64^0x0, 64^0x8000_0000);
  assert(data == 0x020304);
  write_ram(64, 4, 64^0x0, 64^0x7fff_ffff, 0xA1B2C3D4);
  let data = read_ram(64, 3, 64^0x0, 64^0x8000_0000);
  assert(data == 0xA1B2C3);
  print_endline("ok");
}