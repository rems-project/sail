
val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}
val _reg_deref = "reg_deref" : forall ('a : Type). register('a) -> 'a

struct cr = {
  CR0 : bits(4),
  CR1 : bits(2),
  CR2 : bits(2)
}

val _set_CR0 : (register(cr), bits(4)) -> unit effect {wreg}
val _get_CR0 : register(cr) -> bits(4) effect {rreg}

val _set_CR1 : (register(cr), bits(2)) -> unit effect {wreg}
val _get_CR1 : register(cr) -> bits(2) effect {rreg}

val _set_CR2 : (register(cr), bits(2)) -> unit effect {wreg}
val _get_CR2 : register(cr) -> bits(2) effect {rreg}

function _set_CR0 (cr_ref, v) = {
  cr = _reg_deref(cr_ref);
  cr.CR0 = v;
  (*cr_ref) = cr;
}
function _get_CR0 cr = reg_deref(cr).CR0

function _set_CR1 (cr_ref, v) = {
  cr = _reg_deref(cr_ref);
  cr.CR1 = v;
  (*cr_ref) = cr;
}
function _get_CR1 cr = reg_deref(cr).CR1

function _set_CR2 (cr_ref, v) = {
  cr = _reg_deref(cr_ref);
  cr.CR2 = v;
  (*cr_ref) = cr;
}
function _get_CR2 cr = reg_deref(cr).CR2

overload _mod_CR0 = {_set_CR0, _get_CR0}
overload _mod_CR1 = {_set_CR1, _get_CR1}
overload _mod_CR2 = {_set_CR2, _get_CR2}

val _get_cr : register(cr) -> bits(8) effect {rreg}

function _get_cr cr_ref =
  let cr = reg_deref(cr_ref) in cr.CR0 @ cr.CR1 @ cr.CR2

val _set_cr : (register(cr), bits(8)) -> unit effect {wreg}

function _set_cr (cr_ref, v) = {
  cr = _reg_deref(cr_ref);
  cr.CR0 = v[7 .. 4];
  cr.CR1 = v[3 .. 2];
  cr.CR2 = v[1 .. 0];
  (*cr_ref) = cr
}

overload _mod_cr = {_set_cr, _get_cr}

register CR : cr

val main : unit -> unit effect {wreg, rreg}

function main () = {
  CR->cr() = 0x00;
  print_bits("CR = ", CR->cr());
  CR->cr() = 0xCA;
  print_bits("CR = ", CR->cr());
  print_bits("CR.CR0 = ", CR->CR0());
  print_bits("CR.CR1 = ", CR->CR1());
  print_bits("CR.CR2 = ", CR->CR2());
  CR->CR0() = 0xF;
  print_bits("CR = ", CR->cr());
  CR->CR2() = 0b00;
  print_bits("CR = ", CR->cr());
  ()
}