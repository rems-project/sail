default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

struct Foo('n: Int), 'n <= 64 = {
  field: bits('n)
}

type Foo32 = Foo(32)

function bar(foo: Foo32) -> unit = {
  if foo.field == 0xFFFF_FFFF then {
    print_endline("A")
  } else {
    print_endline("B")
  }
}

function main((): unit) -> unit = {
  let x: Foo32 = struct { field = 0xFFFF_FFFF };
  bar(x)
}
