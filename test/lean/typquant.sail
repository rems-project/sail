default Order dec

$include <prelude.sail>

val foo : forall 'n, 'n > 0. int('n) -> bits(4)

function foo(n) = {
  0xF
}

val foo2 : forall 'n, 'n > 0. int('n) -> bits('n)

function foo2(n) = {
  sail_zeros(n)
}

val bar : forall 'n. bits('n) -> bits('n)

function bar(x) = {
  x
}

val two_tuples : ((string, string), (string, string)) -> string
function two_tuples((x, y), (z, t)) = y

val two_tuples_atom : forall 'n, 'n >= 0. ((string, int('n)), (string, string)) -> bits('n)
function two_tuples_atom((x, y), (z, t)) = sail_zeros(y)

val tuple_of_tuple : ((string, string)) -> string
function tuple_of_tuple(s1, s2) = s1

function use_tuple_of_tuple(s : string) -> string = {
  // tutuple(s, s);
  tuple_of_tuple((s, s))
}


val hex_bits_signed2 : forall 'nn, 'nn > 0. bits('nn) <-> (int('nn), string)

function hex_bits_signed2_forwards(bv) = {
  let len = length(bv);
  let s = if bv[len - 1] == bitone then {
    "stub1"
  } else {
    "stub2"
  };
  (length(bv), s)
}

function hex_bits_signed2_forwards_matches(bv) = true

function hex_bits_signed2_backwards(notn, str) = {
  if str == "-" then {
    sail_zeros(notn)
  } else {
    let parsed = sail_zeros(notn);
    if parsed[notn - 1] == bitzero then {
      parsed
    } else {
      sail_zeros(notn)
    }
  }
}

function hex_bits_signed2_backwards_matches(n, str) = true

 newtype virtaddr = virtaddr : bits(32)

function test_constr (virtaddr(addr) : virtaddr) -> bits(32) = addr
