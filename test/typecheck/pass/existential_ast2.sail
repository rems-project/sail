default Order dec

$include <prelude.sail>

type datasize('n: Int) -> Bool = 'n in {32, 64}

type regno = range(0, 31)

union ast = {
  Ctor1 : {'d, datasize('d). (nat, int('d), bits(4))},
  Ctor2 : {'d, datasize('d). (int, int('d), bits(4))},
}

val decode : bits(16) -> option(ast)

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000110) = {
  let x : {|32, 64|} = if b == 0b0 then 32 else 64;
  let a = unsigned(a);

  Some(Ctor1(a, x, c))
}

function clause decode(a : bits(4) @ b : bits(1) @ c : bits(4) @ 0b0000111) = {
  let x : {|32, 64|} = if b == 0b0 then 32 else 64;
  let a = unsigned(a);

  Some(Ctor2(a, x, c))
}
