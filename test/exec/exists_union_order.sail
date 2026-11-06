default Order dec
$include <prelude.sail>

// Test existing type on a constructor argument, with some pattern matching and a let-bound tuple argument.

union Foo = {
  Bar : {'n 'm, 'n in {1,2,4} & 'm in {1,2,4}. (int('n), int('m), bits(8 * 'n), bits(8 * 'm))}
}

function f1() -> Foo = Bar (2, 1, 0x1234, 0x56)
function f2() -> Foo =
  let x : {'m 'n, 'n in {1,2,4} & 'm in {1,2,4}. (int('n), int('m), bits(8 * 'n), bits(8 * 'm))} = (2, 1, 0x1234, 0x56) in Bar(x)

function g(x : Foo) -> int =
  match x {
    Bar (n,m,v,w) => n - m + unsigned(v) + unsigned(w)
  }

function main() -> unit = {
  let i = g(f1());
  let j = g(f2());
  print_int("i = ", i);
  print_int("j = ", j)
}
