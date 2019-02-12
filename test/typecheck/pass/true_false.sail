default Order dec

$include <prelude.sail>

function main((): unit) -> unit = {
  let x: bool(false) = false;
  let y: bool(true) = true;
  _check(x : bool);
  _check(x : bool(false));
  _not_check(x : bool(true))
}
