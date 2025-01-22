default Order dec

$include <prelude.sail>

$[no_enum_number_conversions]
enum E = A | B | C

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
