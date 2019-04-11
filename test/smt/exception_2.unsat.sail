default Order dec

$include <vector_dec.sail>

union exception = {
  E_bool : bool,
  E_unit : unit
}

register R : bool

$property
function prop((): unit) -> bool = {
  try {
    if R then {
       throw(E_bool(true))
    } else {
       true
    }
  } catch {
    E_bool(b) => b,
    E_unit() => false
  }
}
