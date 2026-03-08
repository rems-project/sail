default Order dec

$include <prelude.sail>
$include <option.sail>
$include <string.sail>

type AC_error = unit

union A_error = {
  A_unit : unit,
  A_custom : AC_error
}

type BC_error = unit

union B_error = {
  B_unit : unit,
  B_custom : BC_error
}

val convert_custom : AC_error -> BC_error

function convert_custom(_) = ()

function foo(z: int, x: A_error) -> B_error = {
  let e: B_error = match (z, x) {
    (_, A_custom(e)) => B_custom(convert_custom(e)),
    (_, A_unit())  => B_unit(),
  } in  { e };
}

val main : unit -> unit

function main() = {
  let _ = foo(3, A_custom());
  print_endline("ok")
}