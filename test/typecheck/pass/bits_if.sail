default Order dec
$include <prelude.sail>

val f : forall ('b : Bool). (bool('b), bits(if 'b then 32 else 64)) -> int

function f(_, v) = unsigned(v)

val main : unit -> unit

function main() = {
  assert(f(true, 0x00000001) == 1);
  assert(f(false, 0x0000000000000002) == 2);
}
