default Order dec

$include <prelude.sail>

function recursive(x: int) -> int =
  if x >= 0 then x else recursive(x + 1)
