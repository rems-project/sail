default Order dec

$include <prelude.sail>

type xlen = 32

type regbits = bits(5)

$span start EX_REGBITS
register R1 : bits(xlen)
register R2 : bits(xlen)

function access_register(r : regbits) -> bits(xlen) = {
  match r {
     0b00000 => 0x0000_0000, // zero register
     0b00001 => R1,
     0b00010 => R2,
     // and so on
  }
}
$span end
