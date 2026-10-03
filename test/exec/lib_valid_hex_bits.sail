default Order dec

$include <prelude.sail>
$include <hex_bits.sail>

overload not = {not_bool}

val main : unit -> unit

function main() = {
  foreach (n from 1 to 64) {
    assert(not(valid_hex_bits(n, "not_hex_bits")));
  };

  assert(valid_hex_bits(1, "0x0"));
  assert(valid_hex_bits(1, "0x1"));
  assert(not(valid_hex_bits(1, "0x2")));
  assert(not(valid_hex_bits(1, "0x3")));
  assert(not(valid_hex_bits(1, "0x4")));
  assert(not(valid_hex_bits(1, "0x5")));
  assert(not(valid_hex_bits(1, "0x6")));
  assert(not(valid_hex_bits(1, "0x7")));
  assert(not(valid_hex_bits(1, "0x8")));
  assert(not(valid_hex_bits(1, "0x9")));
  assert(not(valid_hex_bits(1, "0xA")));
  assert(not(valid_hex_bits(1, "0xB")));
  assert(not(valid_hex_bits(1, "0xC")));
  assert(not(valid_hex_bits(1, "0xD")));
  assert(not(valid_hex_bits(1, "0xE")));
  assert(not(valid_hex_bits(1, "0xF")));

  assert(valid_hex_bits(2, "0x0"));
  assert(valid_hex_bits(2, "0x00"));
  assert(valid_hex_bits(2, "0x000"));
  assert(valid_hex_bits(2, "0x0000"));

  assert(valid_hex_bits(2, "0x3"));
  assert(valid_hex_bits(2, "0x02"));
  assert(valid_hex_bits(2, "0x001"));
  assert(valid_hex_bits(2, "0x0003"));

  assert(valid_hex_bits(2, "0x3"));
  assert(valid_hex_bits(2, "0x02"));
  assert(valid_hex_bits(2, "0x001"));
  assert(valid_hex_bits(2, "0x0003"));

  assert(valid_hex_bits(8, "0xFF"));
  assert(valid_hex_bits(8, "0x0FF"));
  assert(not(valid_hex_bits(8, "0xZF")));
  assert(not(valid_hex_bits(8, "0x0ZF")));
  assert(not(valid_hex_bits(8, "0xFZ")));
  assert(not(valid_hex_bits(8, "0x0FZ")));
  assert(not(valid_hex_bits(8, "0xZ0FZ")));

  print_endline("ok");
}
