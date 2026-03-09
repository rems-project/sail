default Order dec
$include <prelude.sail>

function test_loop () -> int = {
  var x : int = 0;
  var y : int = 0;
  while x < 10 do {
    y = y + x;
  };
  y
}

function test_rec (x : int) -> int = {
  if x < 0 then 0 else 1 + test_rec (x - 1)
}

