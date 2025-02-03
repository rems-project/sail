default Order dec

$include <prelude.sail>

function match_option(x : option(bit)) -> bit = {
  match x {
    Some(x) => x,
    None() => bitzero,
  }
}

function option_match(x : option(unit), y : bit) -> option(bit) = {
    match x {
        Some(()) => Some(y),
        None() => None()
    }
}