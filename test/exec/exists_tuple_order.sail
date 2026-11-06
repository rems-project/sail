default Order dec
$include <prelude.sail>

// Test existentially typed tuples returned from functions, swapping the order of the type variables.

function f1() -> {'n 'm, 'n in {1,2,4} & 'm in {1,2,4}. (int('n), int('m), bits(8 * 'n), bits(8 * 'm))} = (2, 1, 0x1234, 0x56)
function f2() -> {'m 'n, 'n in {1,2,4} & 'm in {1,2,4}. (int('n), int('m), bits(8 * 'n), bits(8 * 'm))} = (2, 1, 0x1234, 0x56)

function g(x : {'m 'n, 'm in {1,2,4} & 'n in {1,2,4}. (int('n), int('m), bits(8 * 'n), bits(8 * 'm))}) -> int =
  let (n,m,v,w) = x in
  n - m + unsigned(v) + unsigned(w)

function main() -> unit = {
  let i = g(f1());
  let j = g(f2());
  print_int("i = ", i);
  print_int("j = ", j)
}
