default Order dec

$include <prelude.sail>

type xlen : Int = 64

bitfield Sysreg : bits(32) = {
  A : 5,
  B : 4
}

register sysreg : Sysreg

function read_sysreg code : bits(2) -> bits(xlen) = {
  sysreg.bits = 0x0000_FFFF;
  let res: bits(xlen) = match (code, sizeof(xlen)) {
    (0b00, _) => 0x0000_0000_0000_0000,
    (0b01, 32) => sysreg.bits(),
    (0b01, _) => 0x0000_0000_0000_0001, 
    (0b10, _) => 0x0000_0000_0000_0010, 
    (0b11, _) => 0x0000_0000_0000_0011, 
  };
  print_bits("sysreg = ", sysreg.bits);
  res
}

function main() -> unit = {
  let _ = read_sysreg(0b01);
  ()
}
