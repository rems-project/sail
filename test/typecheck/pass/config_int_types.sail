default Order dec

$include <prelude.sail>

$option --config ../typecheck/pass/config_int_types.json

type len = 32

function blackbox() -> int = {
  signed(undefined : bits(5))
}

function main() -> unit = {
  let _ : range(0, 16) = config c1;
  let _ : range(0, len) = config c2;
  let _ : int(32) = config c3;
  let _ : {'n, true & 'n >= 32 & not('n == 64). int('n)} = config c4;
  let n as int('n) = blackbox();
  if n == 64 then {
    let _ : int('n) = config c5;
  }
}
