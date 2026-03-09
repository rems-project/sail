default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

union ast = {
  Foo : {'n, 'n in {16,32}. (int, int, int('n), bits('n))},
  Bar : (int, int, {'n, 'n in {16,32}. (int('n), bits('n))}),
}

val fst : forall ('s 't : Type). ( ('s, 't) ) -> 's
function fst( (s, _) ) = s

val snd : forall ('s 't : Type). ( ('s, 't) ) -> 't
function snd( (_, t) ) = t

function test4c(i : int, v : bits(16)) -> ast =
  let x : (int, {'n, 'n in {16, 32}. (int, int, int('n), bits('n))}) = (i,(i,i,16,v)) in
  Foo(snd(x))
