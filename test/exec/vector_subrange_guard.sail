default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  let x : bits(8) = 0xAB;
  match x {
    v[3..0] @ v[7..4] if v == 0xBA => {
      print_endline("ok")
    },
    _ => (),
  }
}
