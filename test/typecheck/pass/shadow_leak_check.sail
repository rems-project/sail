default Order dec

function some_int() -> int = {
  4
}

function some_other_int() -> int = {
  5
}

val test : forall 'n 'm, 'n == 'm. (int('n), int('m)) -> unit

function main() -> unit = {
  let 'x = some_int();

  let 'y: int('x) = {
     let 'x = some_other_int();
     x
  };

  _prove(constraint('x == 'y));

  test(x, y)
}
