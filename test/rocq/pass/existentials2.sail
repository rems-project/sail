default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

union ast = {
  Foo : {'n, 'n in {16,32}. (int, int, int('n), bits('n))},
  Bar : (int, int, {'n, 'n in {16,32}. (int('n), bits('n))}),
}

struct st = {
  One : (int, int),
  Two : {'n, 'n in {16, 32}. (int('n), bits('n))},
  Three : (int, {'n, 'n in {16, 32}. (int('n), bits('n))}),
}

function test_struct1(i : int, v : bits(16)) -> st = struct {
  One = (i,i),
  Two = (16, v),
  Three = (i, (16, v)),
}

function test_struct2(i : int, v : bits(16), st0 : st) -> st = {
  var st1 = st0;
  st1.Two = (16, v);
  st1.Three = (i, (16, v));
  st1
}

union ast2 = {
  Foo2 : {'n, 'n in {16,32}. (int, (int('n), bits('n)))},
}

function test11(x : ast2) -> int =
  match x {
  Foo2 (y, z) => match z { (_,v) => unsigned(v) }
  }

function test12(i : int, v : bits(16)) -> ast2 = Foo2(i,(16,v))
