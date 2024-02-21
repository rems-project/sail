default Order dec

$include <prelude.sail>

mapping Foo : bits(2) <-> int = {
  0b00 <-> 10,
  0b01 <-> 1,
  forwards _ => 5,
  backwards _ => 0b11
}
