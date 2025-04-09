default Order dec

$include <prelude.sail>

outcome test : int('n) -> unit with 'n

outcome test2 : int('n) -> unit with 'n

instantiation test with 'n = 32

instantiation test2 with 'n = 64

function main() -> unit = {
  test(32)
}
