default Order dec

$include <prelude.sail>
$include <mapping.sail>

function main() -> unit = {
  print_bits("1. ", hex_parse(8, "0xaB"));
  print_endline(hex_string(0xAB));
}