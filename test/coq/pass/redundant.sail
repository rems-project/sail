default Order dec
$include <prelude.sail>

/* The current guarded pattern rewrite can produce results with redundant clauses.
   Rocq rejects these extra clauses.  This test is structured to trigger this,
   and check that the redundant patterns have been removed. */

union t = {
  Hello : int,
  World : int,
}

function foo(x : t) -> int = match x { Hello(y) => y, World(y) => y }

function test(x : (bool, t)) -> bool =
  match x {
    (_, Hello(x)) if x > 0 => true,
    (true, y) if foo(y) > 0 => true,
    (_, Hello(x)) => false,
    (_, _) => false,
  }
