default Order dec

$include <prelude.sail>

union Foo = {
  Bar : bits(32)
}

mapping baz : Foo <-> bits(32) = {
  Bar(imm) <-> imm[31 .. 16] @ imm[15 .. 0]
}
