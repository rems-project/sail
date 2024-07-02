default Order dec

$include <prelude.sail>

register R : vector(32, option(bits(16))) = vector_init(None())

val main : unit -> unit

function main() = {
  match R[0] {
    None() => {
      print_endline("ok");
      R[0] = Some(0xFFFF)
    },
    _ => (),
  };
  match R[0] {
    Some(0xFFFF) => print_endline("ok"),
    _ => (),
  };

  var v : vector(4, int) = vector_init(0);
  v[0] = 1;
  v[1] = 2;
  v[2] = 3;
  v[3] = 9223372036854775807000;

  foreach (i from 0 to 3) {
    print_int("v[i] = ", v[i])
  }
}
