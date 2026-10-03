default Order dec

$include <arith.sail>
$include <vector_dec.sail>

type xlen : Int = 32
type xlenbits = bits(xlen)

register reg : bits(64)

function read_xlen (arg : bool) -> xlenbits = {
  match (arg, sizeof(xlen)) {
    (_, 32) => reg[31 .. 0],
    (_, 64) => reg,
    (_, _)  => if   sizeof(xlen) == 32
               then reg[31 .. 0]
	       else reg[63 .. 32]
  }
}

type ylen : Int = 64
type ylenbits = bits(ylen)

function read_ylen (arg : bool) -> ylenbits = {
  match (arg, sizeof(ylen)) {
    (_, 32) => reg[31 .. 0],
    (_, 64) => reg,
    (_, _)  => if   sizeof(ylen) == 32
               then reg[31 .. 0]
	       else reg
  }
}

val main : unit -> unit effect {rreg, wreg}
function main() = {
  reg = 0xABCD_1234_5678_EF91;
  let v = read_xlen(true);
  print_bits("v = ", v);
  let v = read_ylen(true);
  print_bits("v = ", v);
  ()
}
