default Order dec

$include <prelude.sail>
$include <arith.sail>

function foreachloop(m : nat, n : nat) -> int = {
  var res : int = 0;
  foreach (i from m to n) {
    res = res + 1;
  };
  res
}

/*
function whileloop(n : nat) -> int = {
  var res : int = 0;
  while res < n do {
    if res == 3 then {
      res = res + 1;
    } else {
      res = res + 4;
    }
  };
  res
}
*/
