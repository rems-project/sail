default Order dec

$include <prelude.sail>

val foo : forall 'a 'b 'c. (bool('a), bool('b), bool('c), bool(if 'a then 'b else 'c)) -> unit

function foo(a, b, c, ite) = {
  if a & ite then {
    let _ : bool('b) = ite;
    let _ : bool(if 'a then 'b else 'c) = b;
    _prove(constraint('b));
    _prove(constraint(if 'a then true else false));
    if c then {
      _prove(constraint(if 'a then 'b else 'c))
    }
  }
}
