default Order dec

register R : int

val foo : int(1) -> unit
val bar : int(2) -> unit

function main((): unit) -> unit = {
  let 'x : {'z, 'z == 1. int('z)} = 1;
  let 'y = x;
  foo(x);
  let 'x : {'z, 'z == 2. int('z)} = 2;
  foo(y);
}