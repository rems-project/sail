default Order dec

$include <prelude.sail>

function extern_add() -> int = {
  return add_int(5, 4)
}

function extern_sub() -> int = {
  return sub_int(5, 4)
}

function extern_sub_nat() -> nat = {
  return sub_nat(5, 4)
}

function extern_tdiv() -> int = {
  return tdiv_int(5, 4)
}

function extern_tmod() -> int = {
  return tmod_int(5, 4)
}

function extern_tmod_positive() -> int = {
  return _tmod_int_positive(5, 4)
}

function extern_negate() -> int = {
  return negate_int(5)
}

function extern_mult() -> int = {
  return mult_int(5, 4)
}

function extern_and() -> bool = {
  return and_bool(true, false)
}

function extern_and_no_flow() -> bool = {
  return and_bool_no_flow(true, false)
}

function extern_or() -> bool = {
  return or_bool(true, false)
}

function extern_eq_bool() -> bool = {
  return eq_bool(true, false)
}

function extern_eq_bit() -> bool = {
  return eq_bit(bitzero, bitone)
}

