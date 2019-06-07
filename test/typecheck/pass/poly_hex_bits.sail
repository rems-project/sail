default Order dec

$include <prelude.sail>

val hex_bits : forall 'n, 'n >= 0. implicit('n) -> string <-> bits('n)

function test() -> unit = {
  match "0x0F" {
    x <- hex_bits(5) if x == 0b01111 => (),
    _ => ()
  }
}
