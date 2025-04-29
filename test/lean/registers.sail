default Order dec

$include <prelude.sail>

register R0 : bits(64)
register R1 : bits(64)
register INT : int
register BOOL : bool
register NAT : nat
register BIT : bit

function test () -> int = {
  INT = INT + 1;
  INT
}

struct My_struct = {
  field1 : int,
  field2 : bit,
}

function test_reg_if_struct (x : My_struct, b : bool) -> My_struct = {
  let y = { x with field1 = if b then INT else 3 };
  { y with field1 = if BOOL then INT else 3 }
}
