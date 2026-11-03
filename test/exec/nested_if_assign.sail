default Order dec
$include <prelude.sail>

function f(b: bool) -> int = {
  var i : int = 0;
  let x = if b then
    if i < 10 then (i = i + 2, true) else (i = i + 3, true)
  else ((), true);
  i
}

function main() -> unit = assert(f(true) == 2)
