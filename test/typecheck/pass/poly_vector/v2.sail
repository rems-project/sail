default Order dec

$include <prelude.sail>

type bitvector('n, 'ord: Order) = vector('n, 'ord, bit)

val "to_generic" : forall 'n. bitvector('n, dec) -> vector('n, dec, bit)

val "print_endline" : string -> unit

function my_length forall 'n ('a : Type). (xs: vector('n, dec, 'a)) -> int('n) = {
  length(xs)
}

function main() -> unit = {
  let xs : bits(32) = 0xFFFF_FFFF;
  if my_length(to_generic(xs)) == 32 then {
    print_endline("ok")
  } else {
    print_endline("false")
  }
}
