$ifndef _SMT_TEST_ARCH
$define _SMT_TEST_ARCH

$include <regfp.sail>

register x0 : bits(32)
register x1 : bits(32)
register x2 : bits(32)
register x3 : bits(32)

function wX(r: bits(2), v: bits(32)) -> unit = {
  match r {
    0b00 => x0 = v,
    0b01 => x1 = v,
    0b10 => x2 = v,
    0b11 => x3 = v
  }
}

function rX(r: bits(2)) -> bits(32) = {
  match r {
    0b00 => x0,
    0b01 => x1,
    0b10 => x2,
    0b11 => x3
  }
}

overload X = {rX, wX}

function arch_load(rd: bits(2), rs: bits(2)) -> bool = {
  X(rd) = __read_mem(Read_plain, 32, X(rs), 4);
  true
}

function arch_store(rd: bits(2), rs: bits(2)) -> bool = {
  let addr = X(rd);
  __write_mem(Write_plain, 32, addr, 4, X(rs))
}

$endif
