default Order dec

$include <prelude.sail>

newtype wrapper = Wrapper : bits(5)

newtype constrained('n), 'n in {32, 64} = C : int('n)

function main() -> unit = {
  let x = Wrapper(0b00100);
  match x {
    Wrapper(y) => print_bits("y = ", y)
  };
  let z = C(32);
  match z {
    C(w) => print_int("w = ", w)
  }
}
