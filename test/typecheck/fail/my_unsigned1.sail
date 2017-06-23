
default Order inc

val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o >= 0, 'o + 1 <= 2**'m. vector<'n,'m,'ord,bit> -> [:'o:] effect pure my_unsigned

let MAX = my_unsigned(0xff)

let ([:0:]) MIN = MAX