default Order dec
$include <prelude.sail>

enum t = {A, B, C}

val test1 : t -> bool
val test2 : int -> bool

scattered function test1

function clause test1(A) = false
function clause test1(B) = test2(5)
function clause test1(C) = true

end test1

function test2(x) = {
  if x > 0 then true else if x == 0 then test1(A) else test1(B)
}

termination_measure test1(x) = match x { A => 0, B => 1, C => 0 }
termination_measure test2(x) = if x <= 0 then 2 else 0

function main() -> unit = {
  assert(test2(10));
  assert(not_bool(test2(0)));
  assert(test2(-10));
}
