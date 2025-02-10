default Order dec

$include <prelude.sail>
$include <generic_equality.sail>
$include <mapping.sail>

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

function extern__shl8() -> int = {
  return _shl8(8, 2)
}

function extern__shl32() -> int = {
  return _shl32(32, 1)
}

function extern__shl1() -> int = {
  return _shl1(1, 2)
}

function extern__shl_int() -> int = {
  return _shl_int(4, 2)
}

function extern__shr32() -> int = {
  return _shr32(30, 1)
}

function extern__shr_int() -> int = {
  return _shr_int(8, 2)
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

function extern_vector_update() -> vector(5, dec, int) = {
  vector_update([23, 23, 23, 23, 23], 2, 42)
}

/* Testing mapping.sail */

function extern_string_take() -> string = {
  return string_take("Hello, world", 5)
}

function extern_string_drop() -> string = {
  return string_drop("Hello, world", 5)
}

function extern_string_length() -> int = {
  return string_length("Hello, world")
}

function extern_string_append() -> string = {
  return string_append("Hello, ", "world")
}

function extern_string_startswith() -> bool = {
  return string_startswith("Hello, world", "Hello")
}
