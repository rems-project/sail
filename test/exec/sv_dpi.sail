default Order dec

$include <prelude.sail>

$iftarget systemverilog

$option --sv-verilate-args "include/sv_dpi.cpp"

$[sv_function { types = ["int", "int"], return_type = "int", dpi = true }]
val foo = impure "sv_dpi_foo" : (int, int) -> int

$else

function foo(x : int, y : int) -> int = x + y

$endif

val main : unit -> unit

function main() = {
  let x = foo(2, 5);
  print_int("x = ", x)
}
