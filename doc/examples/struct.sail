default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

struct My_struct = {
  field1 : bits(5),
  field2 : int,
  field3 : string,
}

val example : unit -> unit

function example() = {
  // Struct literals are created with the struct keyword
  let s : My_struct = struct {
    field1 = 0b11111,
    field2 = 5,
    field3 = "test",
  };

  // Accessing a struct field, prints "field1 is 0b11111"
  print_bits("field1 is ", s.field1);

  // Updating struct fields, creating a new struct variable s2
  var s2 = { s with field1 = 0b00000, field3 = "a string" };

  // Prints "field1 is 0b00000"
  print_bits("field1 is ", s2.field1);
  // Prints "field2 is 5", as field2 was taken from 's' and not modified
  print_int("field2 is ", s2.field2);

  // Because s2 is mutable we can assign to it
  s2.field3 = "some string";
  // Prints "some string"
  print_endline(s2.field3)
}

struct My_other_struct('n : Int, 'a : Type) = {
  a_bitvector : bits('n),
  something : 'a
}

val poly_example : unit -> unit

function poly_example() = {
  var s3 : My_other_struct(2, string) = struct {
    a_bitvector = 0b00,
    something = "a string"
  };

  var s4 : My_other_struct(32, My_struct) = struct {
    a_bitvector = 0xFFFF_FFFF,
    something = struct {
      field1 = 0b11111,
      field2 = 6,
      field3 = "nested structs!",
    }
  };

  s3.a_bitvector = 0b11;

  // Note that once created, we cannot change a variable's type, so the following is forbidden:
  // s3.a_bitvector = 0xFFFF_FFFF;

  // Changing the type is also forbidden in a with expression:
  // let s4 : My_other_struct(32, string) = { s3 with a_bitvector = 0xFFFF_FFFF };

  // If structs are nested, then field accesses can also be nested
  print_endline(s4.something.field3);
  // and assignments
  s4.something.field3 = "another string"
}
