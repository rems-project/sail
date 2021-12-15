default Order dec

$sail_internal

type bits ('n : Int) = bitvector('n, dec)

union option ('a : Type) = {
  Some : 'a,
  None : unit
}

struct test = {
  bits1 : bits(32),
  bits2 : bits(32)
}

val "print_int" : (string, int) -> unit

val main : unit -> unit

function main() = {
  let x : int = 3;
  let y = Some((x, struct { bits1 = 0xDEADBEEF, bits2 = 0xCAFECAFE } : test));
  match y {
    Some(q, w) => print_int("q = ", q),
    None()     => ()
  }
}