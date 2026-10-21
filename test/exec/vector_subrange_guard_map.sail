default Order dec

$include <prelude.sail>

val main : unit -> unit

union eTest = {
  A : (bits(8)),
}

mapping mTest : eTest <-> bits(8) = {
  A(v) <-> v[3 ..0] @ v[7..4] when v == 0xBA,
}

function main() = {
  let x : eTest = mTest(0xAB);
  match x {
    A(v) if v == 0xBA => {
      print_endline("ok")
    },
    _ => (),
  }
}