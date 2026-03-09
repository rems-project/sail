
function test_loop () -> int = {
  var x : int = 0;
  var y : int = 0;
  while x < 5 do {
    y = y * x;
  };
  y
}

function test_rec (x : int) -> int = {
  if x < 0 then 0 else 2 * test_rec (x - 1)
}

