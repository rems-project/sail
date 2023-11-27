default Order dec

$include <prelude.sail>

$span start BITFIELD

bitfield cr_type : bits(8) = {
  CR0 : 7 .. 4,
  LT  : 7,
  GT  : 6,
  CR1 : 3 .. 2,
  CR3 : 1 .. 0
}

register CR : cr_type

$span end

val bitfield_access_example : unit -> unit

function bitfield_access_example() = {
  // Rather than using numeric indices, the bitfield names are used
  let cr0_field : bits(4) = CR[CR0];

  // Bitfield accessors always return bitvector results
  let lt_field : bits(1) = CR[LT]; // Note 'bits(1)' not 'bit'

  // Can access the underlying bitvector using the bits field
  let some_bits : bits(7) = CR.bits[6 .. 0];
}

val bitfield_update_example : unit -> unit

function bitfield_update_example() = {
  // We can set fields on the CR register using their field names
  CR[CR3] = 0b01;

  // If we want to set the underlying bits
  CR.bits[1 .. 0] = 0b01;

  // We can even use vector update notation!
  CR = [CR with CR3 = 0b01, LT = 0b1];

  // Because of the representation, we could set the whole thing like:
  CR = (struct { bits = 0x00 } : cr_type);
}

val legacy_bitfields : unit -> unit

function legacy_bitfields() = {
  // Assigning to a field of a bitfield register
  CR->CR3() = 0b01;
  // '->' notation just means the setter takes the register by reference:
  (ref CR).CR3() = 0b01;

  // Assigning all the bits (now just 'CR.bits = 0x00')
  CR->bits() = 0x00;

  // Accessing a field
  let cr0_field : bits(4) = CR.CR0();

  // Updating a field
  CR = update_CR3(CR, 0b01); // now '[ CR with CR3 = 0b01 ]'

  // Construct a new CR bitfield
  CR = Mk_cr_type(0x00);
}
