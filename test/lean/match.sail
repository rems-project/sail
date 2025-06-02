default Order dec

$include <prelude.sail>

$[no_enum_number_conversions]
enum E = A | B | C

register r_A : E
register r_B : E
register r_C : E

function match_enum(x : E) -> bit = {
  match x {
    A => bitone,
    B => bitone,
    C => bitzero,
  }
}

function match_option(x : option(bit)) -> bit = {
  match x {
    Some(x) => x,
    None() => bitzero,
  }
}

function match_pair_pat((x, y) : (int, int)) -> int = {
  match (x, y) {
    (a, b) => a + b,
  }
}

function match_pair(x : (int, int)) -> int = {
  match x {
    (a, b) => a + b,
  }
}

function match_reg(x : E) -> E = {
  match x {
    A => r_A,
    B => r_B,
    C => r_C,
  }
}

function match_let (x : E, y : int) -> int = {
  match x {
    A => 
    let x = y + y in
    let z = y + y + undefined_int() in
    z + x,
    B => 42,
    C => 23
  }
}

function match_read(x : E) -> unit = {
  r_A = match x {
    A => r_A,
    B => r_B,
    C => r_C,
  }
}

function const16() -> (bitvector(16), bool) = {
  (0xFFFF, true)
}

function const32() -> (bitvector(32), bool) = {
  (0xEEEE_EEEE, false)
}

val match_width : forall 'n, 'n >= 0. bitvector('n) -> bitvector(2 * 'n)
function match_width x = {
  let (foo, _) : (bitvector('n), bool) = match 'n {
    16 => const16(),
    32 => const32(),
    n => (sail_zeros(n), false)
  } in
  bitvector_concat(foo, foo)
}

val match_option_bitvec : (option(bitvector(16))) -> int

function match_option_bitvec (x : option(bitvector(16))) = {
  match x {
    Some(0xFFFF) => 1,
    _ => 0
  }
}

