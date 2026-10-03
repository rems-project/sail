default Order dec

$include <prelude.sail>
$include <string.sail>

type some_bits = {'n, 'n in {16, 32, 64}. bits('n)}

struct if_bits('n: Int) = {
  top: bits(1),
  rest: bits(if 'n == 16 then 15 else if 'n == 32 then 31 else 63),
}

val decompose : forall 'n, 'n in {16, 32, 64}. bits('n) -> if_bits('n)

function decompose(op) = {
  if length(op) == 16 then {
    struct { top = op[15 .. 15], rest = op[14 .. 0] }
  } else if length(op) == 32 then {
    struct { top = op[31 .. 31], rest = op[30 .. 0] }
  } else {
    struct { top = op[63 .. 63], rest = op[62 .. 0] }
  }
}

val if_bits_test : some_bits -> bool

function if_bits_test(op) = {
  let struct { top = _, rest } = decompose(op);
  rest == sail_zeros(length(rest))
}

val main : unit -> unit

function main() = {
  let _ = if_bits_test(0x0000_0000);
  print_endline("ok");
}
