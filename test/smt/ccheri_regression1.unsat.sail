default Order dec

$include <prelude.sail>

val "shiftr" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)

val sub_vec = {c : "sub_bits", _:"sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

infix 4 <_u

function operator <_u forall 'n, 'n >= 0. (x: bits('n), y: bits('n)) -> bool =
  unsigned(x) < unsigned(y)

overload ~ = {not_bool}

$property
function prop() -> bool = {
  let i1 = 0b110 == truncate(shiftr(0x531E02A72708B000, 11), 3);
  let i2 = 0b000 == truncateLSB(0b00001010000011, 3);
  let i3 = 0b101 == sub_vec(0b110, 0b001);
  let i4 = false == operator <_u(0b110, 0b101);
  i1 & i2 & i3 & i4
}