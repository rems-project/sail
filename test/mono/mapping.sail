$include <flow.sail>

/* Trivial example with mapping that doesn't really need monomorphised */

enum foo = {A,B}

mapping map_foo : foo <-> bool = {
  A <-> true,
  B <-> false
}

val run : unit -> unit

function run() = {
  assert(map_foo(A))
}
