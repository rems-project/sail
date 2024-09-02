default Order dec

$include <prelude.sail>
$include <option.sail>

struct S1 = { f1 : int(0) }

struct S2 = { f2 : int }

$property
function prop() -> bool = {
  let x : S1 = struct { f1 = 0 };
  var y : S2 = struct { f2 = 1 };
  y.f2 = x.f1;
  y.f2 == 0
}
