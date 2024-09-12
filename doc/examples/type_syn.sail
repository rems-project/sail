default Order dec

$include <prelude.sail>

type regbits = bits(5)

$span start EX_REGBITS
register R1 : bits(32)
register R2 : bits(32)

function access_register(r : regbits) -> bits(32) = {
  match r {
     0b00000 => 0x0000_0000, // zero register
     0b00001 => R1,
     0b00010 => R2,
     // and so on
  }
}
$span end

type square('n, 'a) = vector('n, vector('n, 'a))
