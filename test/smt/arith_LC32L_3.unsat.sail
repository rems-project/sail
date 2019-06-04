default Order dec

$include <prelude.sail>

$option -smt_ignore_overflow

$property
function prop(x: int, y: int(32), z: int) -> bool = {
  if  -10000 <= x & x <= 10000 & -10000 <= z & z <= 10000 then
    (x * y) * z == x * (y * z)
  else true
}
