default Order dec

$include <prelude.sail>

type LEN : Int = 33

let v : bits(LEN) = 0xFFFF_FFFF

function main((): unit) -> unit = {
  print_bits("v = ", v)
}
