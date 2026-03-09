default Order dec
$include <prelude.sail>
$include <smt.sail>

val load_bytes : forall 'n, 'n >= 0. int('n) -> bits(8 * 'n)

val foo : forall 'n, 'n in {8,16}. (int('n),bool) -> bits('n)

function foo(n,b) = {
  let 'bytes = ediv_int(n,8);
  let data = load_bytes(bytes);
  if b then data else sail_zeros(n)
}
