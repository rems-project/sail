$option -dmagic_hash

default Order dec

$include <prelude.sail>

mapping m : bits(4) <-> bits(8) = {
  x <-> x @ 0xF
}

function main() -> unit = {
  match 0xF {
    x let y = forwards m(x), let z = backwards m(y) => {
      print_bits("x = ", x);
      print_bits("y = ", y);
      print_bits("z = ", z)
    },
    _ => ()
  }
}
