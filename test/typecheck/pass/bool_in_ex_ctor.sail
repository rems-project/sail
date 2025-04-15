default Order dec
$include <prelude.sail>

/* An old unification bug caused a failure when unifying bool and bool(...). */

union ast = {
  Foo : {'n, 'n in {16,32}. (int('n), bits('n), bool)},
}

val decodeFoo : bits(32) -> ast
function decodeFoo(0b010101010101010@[b]@imm) = Foo(16,imm,b == bitzero)
