default Order dec

$include <prelude.sail>
$include <real.sail>

$property
function prop() -> bool = {
  sqrt(4.0) == 2.0;
}
