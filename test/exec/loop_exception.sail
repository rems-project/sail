default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>
$include <string.sail>

$include <exception_basic.sail>

val highest_set_bit : forall ('n : Int), 'n >= 0. bits('n) -> int

overload ~ = {not_bool}

function highest_set_bit x = {
  foreach (i from ('n - 1) to 0 by 1 in dec)
    if x[i] == bitone then return(i) else ();
  return -1
}

val throws : unit -> unit effect {escape}

function throws() = throw Exception()

register R : int

/*
 * Modelling bug described in commit 45554f2893667d951e39c8049631a986c1683857
 */
val fetch_and_execute : unit -> bool effect {escape, wreg, rreg}

function fetch_and_execute() =
{
  R = R + 1;
  try {
    if (R >= 3) then {
      throws()
    };
    true
  } catch {
    Exception() => false
  }
}

val main : unit -> unit effect {escape, wreg, rreg}

function main() =
{
  R = 0;

  /*
   * Expect: "i = 1", "i = 2" and "i = 3"
   */
  foreach (i from 1 to 3) {
    print_int("i = ", i)
  };

  /*
   * Expect: "i = 3", "i = 2" and "i = 1"
   */
  foreach (i from 3 to 1 by 1 in dec) {
    print_int("i = ", i)
  };

  assert(highest_set_bit(0b1) == 0);
  assert(highest_set_bit(0b0010) == 1);
  assert(highest_set_bit(0b10000) == 4);
  assert(highest_set_bit(0x8000_0000_0000_0000) == 63);
  assert(highest_set_bit(0x1_0000_0000_0000_0000) == 64);

  /*
   * Expect: "j = 1", "j = 2" and "j = 3"
   */
  j : int = 0;

  while j < 3 do {
    j = j + 1;
    print_int("j = ", j);
  };

  /*
   * Expect: "k = 0x01", "k = 0x02" and "k = 0x03"
   */
  k : bits(8) = 0x00;

  while unsigned(k) < 3 do {
    k = k + 1;
    print_bits("k = ", k);
  };

  /*
   * Expect: "Caught"
   */
  try {
    while true do {
      throw Exception();
      assert(false, "Unreachable")
    }
  } catch {
    Exception() => print_endline("Caught")
  };

  /*
   * Expect: "Looping"
   */
  caught : bool = false;

  while ~(caught) do {
    try {
      print_endline("Looping");
      throw Exception();
      assert(false, "Unreachable")
    } catch {
      Exception() => caught = true
    }
  };

  /*
   * Expect "Caught inner exception", "Caught outer exception"
   */
  try {
    try throw Exception()
    catch {
      Exception() => {
        print_endline("Caught inner exception");
	throw Exception()
      }
    }
  } catch {
    Exception() => print_endline("Caught outer exception")
  };

  /*
   * Expect "Outer handler"
   */
  try {
    try throw Exception()
    catch {
      /* Exception in catch guard will throw to outer handler */
      Exception() if { throw Exception(); false } => {
        assert(false, "Unreachable");
	throw Exception()
      },
      _ => assert(false, "Unreachable")
    }
  } catch {
    Exception() => print_endline("Outer handler")
  };

  /*
   * Expect "Outer handler"
   */
  try {
    try throws()
    catch {
      /* Exception in catch guard will throw to outer handler */
      Exception() if { throws(); true } => {
        assert(false, "Unreachable");
	throws()
      },
      _ => assert(false, "Unreachable")
    }
  } catch {
    Exception() => print_endline("Outer handler")
  };

  /*
   * Expect "Once"
   */
  repeat {
    print_endline("Once")
  } until true;

  /*
   * Expect "Once"
   */
  once : bool = false;

  repeat {
    print_endline("Once");
    try throw Exception() catch {
      _ => once = true,
      _ => once = false
    }
  } until once;

  /*
   * Expect "ok"
   */
  if try true catch { _ => false } then {
    print_endline("ok")
  };

  /*
   * Expect "ok"
   */
  if try throw Exception() catch { _ => true } then {
    print_endline("ok")
  };

  /*
   * Expect "R = 3"
   */
  while fetch_and_execute() do ();
  print_int("R = ", R);
}