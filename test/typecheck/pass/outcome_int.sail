default Order dec

$include <prelude.sail>

outcome test : int('n) -> unit with 'n

instantiation test with 'n = 32

function main() -> unit = {
  test(32)
}
