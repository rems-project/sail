$ifndef _REVERSE_ENDIANNESS
$define _REVERSE_ENDIANNESS

$ifdef _DEFAULT_DEC

$include <vector_dec.sail>

/* reverse_endianness function set up to ensure it generates good SMT
definitions. The concat/extract pattern may be less efficient in other
backends where these are not primitive operations. */

val reverse_endianness : forall 'n, 'n in {8, 16, 32, 64, 128}. bits('n) -> bits('n)

function reverse_endianness(xs) = {
  let len = length(xs);
  if len == 8 then {
    xs
  } else if len == 16 then {
    xs[7 .. 0] @ xs[15 .. 8]
  } else if len == 32 then {
    xs[7 .. 0] @ xs[15 .. 8] @ xs[23 .. 16] @ xs[31 .. 24]
  } else if len == 64 then {
    xs[7 .. 0] @ xs[15 .. 8] @ xs[23 .. 16] @ xs[31 .. 24] @ xs[39 .. 32] @ xs[47 .. 40] @ xs[55 .. 48] @ xs[63 .. 56]
  } else {
    xs[7 .. 0] @ xs[15 .. 8] @ xs[23 .. 16] @ xs[31 .. 24] @ xs[39 .. 32] @ xs[47 .. 40] @ xs[55 .. 48] @ xs[63 .. 56]
    @ xs[71 .. 64] @ xs[79 .. 72] @ xs[87 .. 80] @ xs[95 .. 88] @ xs[103 .. 96] @ xs[111 .. 104] @ xs[119 .. 112] @ xs[127 .. 120]
  }
}

$endif

$endif
