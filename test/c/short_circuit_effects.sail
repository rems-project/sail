default Order dec

$include <prelude.sail>
$include <string.sail>

// Boolean & and | are short-circuiting: an effectful right-hand operand
// must only be evaluated when the left-hand operand does not already
// determine the result.

register counter : int

val bump : unit -> bool

function bump() = {
  counter = counter + 1;
  true
}

val boom : unit -> bool

function boom() = {
  assert(false, "right-hand operand of a short-circuiting operator was evaluated");
  true
}

val print_bool : (string, bool) -> unit

function print_bool(s, b) = print_endline(concat_str(s, if b then "true" else "false"))

val and_boom : bool -> bool

function and_boom(b) = b & boom()

val or_boom : bool -> bool

function or_boom(b) = b | boom()

val chains : (bool, bool) -> unit

function chains(t, f) = {
  print_bool("f & boom & boom = ", f & boom() & boom());
  print_bool("t & f & boom = ", t & f & boom());
  print_bool("t | boom | boom = ", t | boom() | boom());
  print_bool("f | t | boom = ", f | t | boom());
  print_bool("(f & boom) | t = ", (f & boom()) | t);
  print_bool("(t | boom) & (f | t) = ", (t | boom()) & (f | t))
}

val conditions : (bool, bool) -> unit

function conditions(t, f) = {
  if f & boom() then print_endline("if &: wrong") else print_endline("if &: ok");
  if t | boom() then print_endline("if |: ok") else print_endline("if |: wrong");
  let x = f & boom();
  let y = t | boom();
  print_bool("let & = ", x);
  print_bool("let | = ", y)
}

val side_effects : (bool, bool) -> unit

function side_effects(t, f) = {
  counter = 0;
  let a = f & bump();
  print_int("f & bump: counter = ", counter);
  let b = t | bump();
  print_int("t | bump: counter = ", counter);
  let c = t & bump();
  print_int("t & bump: counter = ", counter);
  let d = f | bump();
  print_int("f | bump: counter = ", counter);
  let e = bump() | boom();
  print_int("bump | boom: counter = ", counter);
  print_bool("results = ", not_bool(a) & b & c & d & e)
}

val pure_operands : (bool, bool) -> unit

function pure_operands(t, f) = {
  print_bool("t & f = ", t & f);
  print_bool("t | f = ", t | f);
  print_bool("f | t & t = ", f | t & t)
}

val main : unit -> unit

function main() = {
  print_bool("f & boom = ", and_boom(false));
  print_bool("t | boom = ", or_boom(true));
  chains(true, false);
  conditions(true, false);
  side_effects(true, false);
  pure_operands(true, false)
}
