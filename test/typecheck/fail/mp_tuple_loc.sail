
enum E = A

mapping foo : (unit, unit) <-> E = {
  ((), ()) <-> A,
}

mapping bar : unit <-> E = {
  () <-> foo((), (), ()),
}

val main : unit -> unit

function main() = {
  let _ : E = bar();
}
