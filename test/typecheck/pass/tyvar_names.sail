default Order dec

$include <prelude.sail>

$option -dmagic_hash

function main((): unit) -> unit = {
  let x = (3 + 3) : {'n, 'n == 6. int('n)};
  _check(x : int('x#0));
  let y = (2 + 4) : {'n, 'n == 6. int('n)};
  _check(y : int('y#0));
  let x = 26 : {'n, 'n == 26. int('n)};
  _check(x : int('x#1));
  ()
}

function main2((): unit) -> unit = {
  let x = (3 + 3) : {'n, 'n == 6. int('n)};
  _check(x : int('x#0));
  let y = (2 + 4) : {'n, 'n == 6. int('n)};
  _check(y : int('y#0));
  let x = 26 : {'n, 'n == 26. int('n)};
  _check(x : int('x#1));
  ()
}