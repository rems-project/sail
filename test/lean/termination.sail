default Order dec
$include <prelude.sail>

enum E = A | B | C

val enabled : E -> bool

val measure : E -> int
function measure(x) = {
  match x {
    A => 10,
    B => 5,
    C => 1,
  }
}

termination_measure enabled(e) = measure(e)

function enabled (e) = {
  match e {
    A => enabled(B),
    B => enabled(C),
    C => true,
  }
}


val measure2 : E -> int
val enabled2 : (bool, E) -> bool

function measure2(x) = {
  match x {
    A => 10,
    B => 5,
    C => 1,
  }
}

termination_measure enabled2(_, x) = measure2(x)

function enabled2 (b, e) = {
  match e {
    A => enabled2(b, B),
    B => enabled2(b, C),
    C => b,
  }
}

