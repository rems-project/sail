default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int(32), z: int) -> bool = {
  let add_comm  = x + y == y + x;
  let add_assoc = (x + y) + z == x + (y + z);
  let add_id  = x + 0 == x;

  add_comm & add_assoc & add_id
}
