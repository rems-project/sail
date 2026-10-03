default Order dec

$include <vector_dec.sail>

function main () : unit->unit = {
  foo = 0xf;
  foo[0] = bitzero;
  print_bits("foo = ", foo)
}