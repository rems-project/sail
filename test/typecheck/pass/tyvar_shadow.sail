default Order dec

$include <prelude.sail>

function main((): unit) -> unit = {
  let x as int('x) = 3;
  let x as int('x) = 4;
  _prove(constraint('x + 'x == 8));
  _not_prove(constraint('x + 'x == 6 | 'x + 'x == 7));

  let y : {'n, 'n == 3. int('n)} = 3;
  _prove(constraint('_y == 3))
}

