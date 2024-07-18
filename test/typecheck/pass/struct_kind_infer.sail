default Order dec

$include <prelude.sail>

struct S('a, 'n) = {
  field1 : 'a,
  field2 : bitvector('n),
}
