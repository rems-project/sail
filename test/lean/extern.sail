default Order dec

$include <prelude.sail>

function extern_negate() -> int = {
  return negate_int(5)
}

function extern_mult() -> int = {
  return mult_int(5, 4)
}

