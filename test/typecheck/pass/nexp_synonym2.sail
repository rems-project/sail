default Order dec

$include <prelude.sail>

type LEN : Int = 30 + 2

type V : Type = bits(LEN)

type V2('n: Int) -> Type = bits('n)

let v : V = 0xFFFF_FFFF

function main((): unit) -> unit = {
  print_bits("v = ", v : V2(LEN))
}
