default Order dec

$include <prelude.sail>

struct S = {
  f1 : int,
  f2 : bool,
}

struct S2 = {
  f1 : int,
  f2 : bool,
}

val main : unit -> unit

function main() = {
  let x : S2 = struct S { f1 = 3, f2 = true };
  ()
}
