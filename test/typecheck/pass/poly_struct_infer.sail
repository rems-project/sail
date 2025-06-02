default Order dec

$include <prelude.sail>

struct S('b, 'a) = {
  f1 : int,
  f2 : 'a,
  f3 : 'b,
}

val main : unit -> unit

function main() = {
  let x = struct S { f1 = 3, f2 = true, f3 = "test" };
  ()
}
