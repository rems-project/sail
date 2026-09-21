default Order dec
$include <prelude.sail>

// A little bit of constant propagation can break mutually recursive function cycles, especially
// for address translation, which is particularly useful for proof assistants.

// Simple example

$option --const-prop-mutrec f
$option --const-prop-mutrec g

val f : (int, bool) -> bool
val g : (int, bool) -> bool

function f(x, b) = {
  if (b) then {
    let c : bool = true;
    assert(true);
    g(x, c)
  } else {
    true
  }
}


function g(x, b) = {
  if (b) then {
    true
  } else {
    let c : bool = false;
    assert(true);
    f(x, c)
  }
}

// Similar, but with enums

enum stage = { First, Second }

$option --const-prop-mutrec fe
$option --const-prop-mutrec ge

val fe : (int, stage) -> bool
val ge : (int, stage) -> bool

function fe(x, b) = {
  match b {
    First => {
      let c : stage = First;
      assert(true);
      ge(x, c)
    },
    Second => true,
  }
}


function ge(x, b) = {
  match b {
    First => {
      let c : stage = Second;
      assert(true);
      fe(x, c)
    },
    Second => true,
  }
}

// A version with a slightly awkward type, essentially a minature example of something seen in the
// RISC-V two-stage address translation.

$option --const-prop-mutrec start
$option --const-prop-mutrec cont

type level('b) = range(0, if 'b then 4 else 3)

val start : (int, bool) -> bool
val cont : forall 'b. (int, bool('b), level('b)) -> bool

val get_init_level : forall 'b. (int, bool('b)) -> level('b)

function get_init_level(x, b) = if b & x > 0 then 4 else 3

function start(x, b) = {
  cont(x, b, get_init_level(x, b))
}

function cont(x, b, level) = {
  if level > 0 then cont(x+1, b, level-1) else if b then start(x, false) else true
}

termination_measure cont(_, _, level) = level

function main () -> unit = {
  assert(f(0, true));
  assert(fe(0, First));
  assert(start(1, true));
}
