default Order dec

$include <vector_dec.sail>

union exception = {
  E_bool : bool,
  E_unit : unit
}

register R : bool

function check_sat((): unit) -> bool = {
  try {
    if R then {
       throw(E_bool(false))
    } else {
       false
    }
  } catch {
    E_bool(b) => b,
    E_unit() => true
  }
}
