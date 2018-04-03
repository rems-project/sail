default Order dec

$include <exception_basic.sail>
$include <flow.sail>

function main (() : unit) -> unit = {
  assert(not_bool(false) == true);
  assert(not_bool(true) == false);
}