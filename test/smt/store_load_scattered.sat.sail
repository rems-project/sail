default Order dec

$include <prelude.sail>
$include <regfp.sail>
$include "test/arch.sail"

scattered union ast

val execute : ast -> bool effect {rmem, rreg, wmv, wreg}

union clause ast = LOAD : (bits(2), bits(2))

function clause execute(LOAD(rd, rs)) = {
  X(rd) = __read_mem(Read_plain, 32, X(rs), 4);
  true
}

union clause ast = STORE : (bits(2), bits(2))

function clause execute(STORE(rd, rs)) = {
  let addr = X(rd);
  __write_mem(Write_plain, 32, addr, 4, X(rs))
}

/* Default memory model is as weak as possible, so this is not true */
$counterexample
function prop() -> bool = {
  let _ = execute(STORE(0b01, 0b10));
  let _ = execute(LOAD(0b00, 0b01));
  X(0b00) == X(0b10)
}
