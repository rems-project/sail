default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

union ast = {
  Foo : {'n, 'n in {16,32}. (int, int, int('n), bits('n))},
  Bar : (int, int, {'n, 'n in {16,32}. (int('n), bits('n))}),
}

function test1(x : ast) -> int = {
  match x {
  Foo(a,b,_,d) => a+b+unsigned(d),
  Bar(a,b,(_,d)) => a+b+unsigned(d),
  }
}

function test2(x : ast) -> int = {
  match x {
  Foo(a,b,_,d) => a+b+unsigned(d),
  Bar(a,b,y) => match y { (_, d) => a+b+unsigned(d) },
  }
}

function test3(x : ast) -> int = {
  match x {
  Foo(a) => match a { (a,b,_,d) => a+b+unsigned(d) },
  Bar(_) => 1,
  }
}

function test4(i : int, v : bits(16)) -> ast =
  let x : {'n, 'n in {16, 32}. (int, int, int('n), bits('n))} = (i,i,16,v) in
  Foo(x)

union ast' = {
  Foo' : {'n, 'n in {16,32}. (int, int, bits('n), int('n))},
}

function test4b(i : int, v : bits(16)) -> ast' =
  let x : {'n, 'n in {16, 32}. (int, int, bits('n), int('n))} = (i,i,v,16) in
  Foo'(x)

function test5() -> unit = {
  let x = Foo(3,3,16,0x1234);
  let y = test4(3,0x1234);
  assert(x == y);
  assert(test1(x) == test2(x));
}

val test6 : (int, {'n, 'n in {16, 32}. (int('n), bits('n))}) -> int

function test6(x, t) = {
  let i : int = match t { (n,v) => unsigned(v) };
  i + x
}

val test7 : (int, (int, {'n, 'n in {16, 32}. (int('n), bits('n))})) -> int

function test7(x, (_, t)) = {
  let i : int = match t { (n,v) => unsigned(v) };
  i + x
}

val test8 : (int, (int, {'n, 'n in {16, 32}. (int('n), bits('n))})) -> int

function test8(x, t) = {
  let i : int = match t { (_, (n,v)) => unsigned(v) };
  i + x
}

val test9 : (int, int) -> {'n, 'n > 0. (int('n), bits('n))}

function test9(n,v) = {
  let n' = if n <= 0 then 1 else n;
  (n', add_bits_int(sail_zeros(n'), v))
}

val test10 : (int, int) -> (int, {'n, 'n > 0. (int('n), bits('n))})

function test10(n,v) = {
  let n' = if n <= 0 then 1 else n;
  (v, (n', add_bits_int(sail_zeros(n'), v)))
}
