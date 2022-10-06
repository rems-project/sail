default Order dec

$include <prelude.sail>

$option -lem_mwords

union phantom_option('a : Type, 'b : Int) = {
  SomeP : 'a,
  NoneP : unit
}

val f : forall ('a : Type) 'n. phantom_option('a, 'n) -> phantom_option('a, 'n + 32)

function f(opt) = match opt {
  SomeP(x) => SomeP(x),
  NoneP()  => NoneP()
}

val test : forall 'n, 'n > 0. int('n) -> phantom_option(bits(8 * 'n), 64)

function test(width) = {
  if 'n == 8 then {
    f(SomeP(sail_zeros(8 * width)))
  } else {
    NoneP()
  }
}
