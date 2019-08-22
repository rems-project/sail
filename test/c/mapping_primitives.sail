default Order dec

$include <prelude.sail>
$include <mapping.sail>

val print = "print_endline" : string -> unit

function main() -> unit = {
  print(hex_string(sail_zeros(0)));
  print(hex_string(0x0));
  print(hex_string(0xABCD));
  print(hex_string(0x00ABCD));
  assert(hex_parse(4, "0xA") == 0xA);
  print(decimal_string(sail_zeros(0)));
  print(decimal_string(0xA));
  print(decimal_string(0x0A));
  print(decimal_string(0xF));
  assert(decimal_parse(8, "12") == 0x0C);
  print(binary_string(sail_zeros(0)));
  print(binary_string(0b00000));
  print(binary_string(0xF));
  print(binary_string(0x000F));
  assert(binary_parse(8, "0b1111") == 0x0F);
}
