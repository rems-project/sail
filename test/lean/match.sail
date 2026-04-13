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


function match_enum2(x : E) -> bit = {
  let y = x;
  bitzero
}

