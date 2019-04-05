default Order dec

$include <vector_dec.sail>

union exception = {
  E_bool : bool,
  E_unit : unit
}

function check_sat((): unit) -> bool = {
  try {
    throw(E_bool(false))
  } catch {
    E_bool(b) => b,
    E_unit() => true
  }
}
