default Order dec

$include <vector_dec.sail>

union exception = {
  E_bool : bool,
  E_unit : unit
}

$property
function prop((): unit) -> bool = {
  try {
    throw(E_bool(true))
  } catch {
    E_bool(b) => b,
    E_unit() => false
  }
}
