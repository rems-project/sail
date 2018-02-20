
val _reg_deref = "reg_deref" : forall ('a : Type). register('a) -> 'a

bitfield cr : bits(8) = {
  CR0 : 7 .. 4,
  LT : 7,
  CR1 : 3 .. 2,
  CR2 : 1,
  CR3 : 0,
}

register CR : cr

bitfield dr : vector(4, inc, bit) = {
  DR0 : 2 .. 3,
  LT : 2
}

register DR : dr

val main : unit -> unit effect {rreg, wreg}

function main () = {
  CR->bits() = 0xFF;
  print_bits("CR: ", CR.bits());
  ref CR.CR0() = 0x0;
  print_bits("CR: ", CR.bits());
  CR->LT() = 0b1;
  print_bits("CR.CR0: ", CR.CR0());
  print_bits("CR: ", CR.bits());
  CR->CR3() = 0b0;
  print_bits("CR: ", CR.bits())
}
