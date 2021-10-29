default Order dec

$include <prelude.sail>
$include <string.sail>

// This file tests that we include the toplevel letbinding in the generated C

$option -c_include includes/xlen_val.h

type xlen: Int = 64

let xlen_val = sizeof(xlen)

val test = { c: "test" } : int(32) -> int(64)

function test(_) = 64

val main : unit -> unit

function main() = {
  print_int("xlen = ", test(32))
}
