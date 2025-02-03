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