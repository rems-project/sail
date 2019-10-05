default Order dec
$include <prelude.sail>
$include <smt.sail>

overload operator % = emod_int

/* The variable p in these tests should have a proof attached at the loop.
   First, tests with pure loop bodies. */

val test1 : forall 'n, 'n > 0. (int('n),int) -> int

function test1(n,m) = {
  p : range(0,'n) = n;
  foreach (i from 0 to m) {
    p = (p + 1) % n;
  };
  p
}

val test2 : forall 'n, 'n > 0. (int('n),int) -> int

function test2(n,m) = {
  p : range(0,'n) = n;
  q : int = 0;
  foreach (i from 0 to m) {
    p = (p + 1) % n;
    q = q + 1;
  };
  p+q
}

val test3 : forall 'n, 'n > 0. (int('n),int) -> int

function test3(n,m) = {
  p : range(0,'n) = n;
  repeat {
    p = (p + 1) % n;
  } until p == 0;
  p
}

termination_measure test3 until p

val test4 : forall 'n, 'n > 0. (int('n),int) -> int

function test4(n,m) = {
  p : range(0,'n) = n;
  q : int = 0;
  repeat {
    p = (p + 1) % n;
    q = q + 1;
  } until p == 0;
  p+q
}

termination_measure test4 until p

/* Now with loop bodies with an assertion */

val test1e : forall 'n, 'n > 0. (int('n),int) -> int effect {escape}

function test1e(n,m) = {
  p : range(0,'n) = n;
  foreach (i from 0 to m) {
    assert(p >= 0);
    p = (p + 1) % n;
  };
  p
}

val test2e : forall 'n, 'n > 0. (int('n),int) -> int effect {escape}

function test2e(n,m) = {
  p : range(0,'n) = n;
  q : int = 0;
  foreach (i from 0 to m) {
    assert(p >= 0);
    p = (p + 1) % n;
    q = q + 1;
  };
  p+q
}

val test3e : forall 'n, 'n > 0. (int('n),int) -> int effect {escape}

function test3e(n,m) = {
  p : range(0,'n) = n;
  repeat {
    assert(p >= 0);
    p = (p + 1) % n;
  } until p == 0;
  p
}

termination_measure test3e until p

val test4e : forall 'n, 'n > 0. (int('n),int) -> int effect {escape}

function test4e(n,m) = {
  p : range(0,'n) = n;
  q : int = 0;
  repeat {
    assert(p >= 0);
    p = (p + 1) % n;
    q = q + 1;
  } until p == 0;
  p+q
}

termination_measure test4e until p
