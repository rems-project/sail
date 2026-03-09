default Order dec
$include <prelude.sail>

$option -const_prop_mutrec f
$option -const_prop_mutrec g

val f : (int, bool) -> bool
val g : (int, bool) -> bool

function f(x, b) = {
  if (b) then {
    let c : bool = true;
    assert(true);
    g(x, c)
  } else {
    true
  }
}


function g(x, b) = {
  if (b) then {
    true
  } else {
    let c : bool = false;
    assert(true);
    f(x, c)
  }
}

function run () -> unit = {
  assert(f(0, true));
}
