default Order dec

$include <prelude.sail>

outcome test : int('n) -> unit with 'n

instantiation test with 'n = bool

function main() -> unit = {
  test(32)
}
