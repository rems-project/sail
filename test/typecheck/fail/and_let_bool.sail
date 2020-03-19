default Order dec

$include <flow.sail>

function test(x) : bool -> bool =
  and_bool(let y : bool = x in not_bool(y), x)
