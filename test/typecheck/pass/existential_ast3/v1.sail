default Order dec

$include <prelude.sail>

type datasize('n: Int) -> Bool = 'n in {32, 64}

union ast = {
  Ctor : {'d 'n, datasize('d) & 0 <= 'n < 'd. (int('d), int('n))}
}

val decode : bits(16) -> option(ast)

// Can have a constrained pair

function clause decode(a : bits(5) @ b : bits(1) @ 0b0000011111) = {
  let (datasize, n) : {'d 'n, datasize('d) & 0 <= 'n < 'd. (int('d), int('n))} =
    if b == 0b0 then (64, unsigned(b @ a)) else (33, unsigned(a));
  Some(Ctor(datasize, n))
}

// Or just lift the function body into the body if the if for flow typing

function clause decode(a : bits(5) @ b : bits(1) @ 0b0000011111) = {
  if b == 0b0 then {
    Some(Ctor(64, unsigned(b @ a)))
  } else {
    Some(Ctor(32, unsigned(a)))
  }
}

// Or use boolean constraint

function clause decode(a : bits(5) @ b : bits(1) @ 0b0000011111) = {
  let 'is_64 = b == 0b0;
  let 'datasize : {'d, ('is_64 & 'd == 64) | (not('is_64) & 'd == 32). int('d)} =
    if is_64 then 64 else 32;
  let n : range(0, 'datasize) = if is_64 then unsigned(b @ a) else unsigned(a);
  None()
}

// Other variants

function clause decode(a : bits(5) @ b : bits(1) @ 0b0000011111) = {
  let (datasize, n) : {'d 'n, datasize('d) & 0 <= 'n < 'd. (int('d), int('n))} =
    if b == 0b0 then {
      let c = unsigned(b @ a);
      (64, c)
    } else (32, unsigned(a));
  Some(Ctor(datasize, n))
}