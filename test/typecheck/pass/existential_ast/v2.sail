default Order dec

$include <prelude.sail>

type datasize('n: Int) -> Bool = 'n in {32, 64}

type regno = range(0, 30)

union ast = {
  Ctor1 : {'d, datasize('d). (bits(4), int('d), bits(4))},
  Ctor2 : {'d, datasize('d). (regno, int('d), bits(4))}
}

val decode : bits(16) -> option(ast)

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000110) = {
  let x : {|32, 64|} = if b == 0b0 then 32 else 64;
  y : {'d, datasize('d). (bits(4), int('d), bits(4))} = (a, x, c);

  Some(Ctor1(y))
}

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000111) = {
  x : {|32, 64|} = if b == 0b0 then 32 else 64;

  Some(Ctor1(a, x, c))
}

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000101) = {
  let x : {|32, 64|} = if b == 0b0 then 32 else 64;

  Some(Ctor1(a, x, c))
}

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000111) = {
  let y = unsigned(a @ 0b0);
  x : {|32, 64|} = if b == 0b0 then 32 else 64;

  Some(Ctor2(y, x, c))
}

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000111) = {
  y = unsigned(a @ 0b0);
  x : {|32, 64|} = if b == 0b0 then 32 else 64;

  Some(Ctor2(y, x, c))
}

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000111) = {
  y = unsigned(a);
  x : {|32, 64|} = if b == 0b0 then 32 else 64;

  Some(Ctor2(y, x, c))
}