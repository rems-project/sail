default Order dec

$include <flow.sail>
$include <arith.sail>
$include <option.sail>
$include <vector_dec.sail>
$include <exception_basic.sail>

val modulus = {ocaml: "modulus", lem: "hardware_mod", coq: "ZEuclid.modulo", _ : "tmod_int"} : forall 'n, 'n > 0 .  (int, atom('n)) -> range(0, 'n - 1)

val add_range = {ocaml: "add_int", lem: "integerAdd", coq: "add_range", c: "add_int"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val sub_range = {ocaml: "sub_int", lem: "integerMinus", coq: "sub_range"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val min = {ocaml: "min_int", lem: "min", coq: "min_atom", c:"min_int"} : forall 'a 'b . (atom('a), atom('b)) -> {'c, ('c == 'a | 'c == 'b) & 'c <= 'a & 'c <= 'b . atom('c)}

overload operator + = {add_range}
overload operator - = {sub_range}

infix 1 >>
infix 1 <<

val "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n) effect {undef}
val "shift_bits_left" : forall 'n 'm. (bits('n), bits('m)) -> bits('n) effect {undef}

val "shiftl" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)
val "shiftr" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)

overload operator >> = {shift_bits_right, shiftr}
overload operator << = {shift_bits_left, shiftl}

val HighestSetBit : forall 'N , 'N >= 2. bits('N) -> {'n, 0 <= 'n < 'N . (bool, atom('n))}

function HighestSetBit x = {
  foreach (i from ('N - 1) to 0 by 1 in dec)
    if [x[i]] == 0b1 then return (true, i);
  return (false, 0)
}

/* hw rounds up E to multiple of 4 */
function roundUp(e) : range(0, 45) -> range(0, 48) =
    let 'r = modulus(e, 4) in
    if (r == 0)
    then e
    else (e - r + 4)

function computeE (rlength) : bits(65) -> range(0, 48) =
    let (nonzero, 'msb) = HighestSetBit((rlength + (rlength >> 6)) >> 19) in
    if nonzero then
      /* above will always return <= 45 because 19 bits of zero are shifted in from right */
      {assert(0 <= msb & msb <= 45); roundUp (min(msb,45)) }
    else
      0

val main : unit -> unit effect {escape}

function main() = {
  let _ = computeE(0xFFFF_FFFF_FFFF_FFFF @ 0b1);
  ()
}
