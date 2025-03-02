default Order dec

$include <prelude.sail>

val example : unit -> unit

function example() = {
  let some_string : string = config some.string_value;
  print_endline(some_string);

  // Booleans are represented as JSON booleans
  let some_bool : bool = config some.bool_value;
  if some_bool then {
    print_endline("some_bool is true")
  };

  // Integers are represented as JSON integers
  let some_int : int = config some.int_value;
  print_int("some_int = ", some_int);

  // Bitvectors have a few allowed representations:
  // We can use a JSON list of booleans
  let some_bits1 : bits(4) = config some.bits_value.one;
  print_bits("some_bits1 = ", some_bits1);

  // That would be unwieldy for larger bitvectors, so we can
  // parse a bitvector from a string with an explicit length.
  let some_bits2 : bits(32) = config some.bits_value.two;
  print_bits("some_bits2 = ", some_bits2);
}
