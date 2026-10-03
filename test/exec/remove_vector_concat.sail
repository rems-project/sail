default Order dec
$include <prelude.sail>

/* An example derived from the RISC-V model that hit typing errors in the Rocq
   and Lean backends because we weren't updating the type environments when
   rewriting vector concatenation patterns away. */

type xlen : Int = 32
constraint xlen in {32, 64}

let xlen = sizeof(xlen)

function predicate(x : int) -> bool = x == 42

val f : bits(6) -> int

function f(x) = 
  match x {
  (0b0 @ v[1..0] @ v [4..3] @ v[2]) if xlen == 32 & predicate(42) => unsigned(v),
  _ => 1
  }

function main() -> unit = print_int("", f(0b011000))
