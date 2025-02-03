default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

/* Testing arith.sail */

function extern_add() -> int = {
  return add_int(5, 4)
}

function extern_sub() -> int = {
  return sub_int(5, -4)
}

function extern_sub_nat() -> nat = {
  return sub_nat(5, 4)
}

function extern_negate() -> int = {
  return negate_int(5)
}

function extern_mult() -> int = {
  return mult_int(5, 4)
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

function extern_max() -> int = {
  return max_int(5, 4)
}

function extern_min() -> int = {
  return min_int(5, 4)
}

function extern_abs_int_plain() -> int = {
  let x: int = -5;
  return abs_int_plain(x)
}

/* Testing flow.sail */

function extern_eq_unit() -> bool = {
  return eq_unit((),())
}

function extern_eq_bit() -> bool = {
  return eq_bit(bitzero, bitone)
}

function extern_not() -> bool = {
  return not_bool(true)
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

function extern_eq_int() -> bool = {
  return eq_int(5, 4)
}

function extern_lteq_int() -> bool = {
  return lteq_int(5, 4)
}

function extern_gteq_int() -> bool = {
  return gteq_int(5, 4)
}

function extern_lt_int() -> bool = {
  return lt_int(5, 4)
}

function extern_gt_int() -> bool = {
  return gt_int(5, 4)
}

/* Testing generic_equality.sail */

function extern_eq_anything() -> bool = {
  return eq_anything(true, true)
}