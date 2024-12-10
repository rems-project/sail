default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

enum My_enum = {
  Foo,
  Bar,
  Baz,
  Quux,
}

enum My_short_enum = A | B | C

val enum_example1 : unit -> unit

function enum_example1() = {
  assert(num_of_My_enum(Foo) == 0);
  assert(num_of_My_enum(Bar) == 1);
  assert(num_of_My_enum(Baz) == 2);
  assert(num_of_My_enum(Quux) == 3);
}

val enum_example2 : unit -> unit

function enum_example2() = {
  assert(My_enum_of_num(0) == Foo)
}

$span start ENUM_CONV
$[enum_number_conversions { from_enum = to_number, to_enum = from_number }]
enum Another_enum = {
  Member1,
  Member2,
}

function custom_conversions() -> unit = {
  assert(to_number(Member1) == 0);
  assert(from_number(1) == Member2);
}
$span end

val iterate : unit -> unit

$span start ENUM_VECTOR
$[enum_vector my_enum_members]
enum My_other_enum = { M1, M2, M3 }

function iterate() = {
  foreach (i from 0 to (length(my_enum_members) - 1)) {
    match my_enum_members[i] {
      M1 => print_endline("1"),
      M2 => print_endline("2"),
      M3 => print_endline("3"),
    }
  }
}
$span end
