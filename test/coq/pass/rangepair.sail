/* Check that tuples of values that should be accompanied by a Coq proof are
   handled properly. */

$include <prelude.sail>

/* Monadic version */

val getpair_eff : unit -> (range(1,2),range(3,4)) effect {escape}

function getpair_eff () = {
  assert(true);
  return (2,3)
}

val test_eff : unit -> range (4,6) effect {escape}

function test_eff () =
  let (x,y) = getpair_eff() in
  x + y

/* Pure version */

val getpair : unit -> (range(1,2),range(3,4))

function getpair () = {
  return (2,3)
}

val test : unit -> range (4,6)

function test () =
  let (x,y) = getpair() in
  x + y
