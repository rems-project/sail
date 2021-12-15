default Order dec

$sail_internal

$include <flow.sail>

val print = "print_endline" : string -> unit

val "print_int" : (string, int) -> unit
val "print_bits" : forall 'n. (string, bitvector('n, dec)) -> unit

union option ('a : Type) = {
  None : unit,
  Some : 'a
}

union soption ('a : Type) = {
  sNone : unit,
  sSome : 'a
}

val main : unit -> unit

function main () = {
  let x : option(int) = Some(5);
  let y : option(int) = None();
  let z : option(bitvector(4, dec)) = Some(0xF);

  match x {
    Some(a) => print_int("a = ", 5),
    None()  => print("None")
  };

  match z {
    Some(b) => print_bits("b = ", b),
    None()  => print("None")
  };

  let q : soption(bitvector(4, dec)) = sSome(0xA);

  match q {
    sSome(c) => print_bits("c = ", c)
  }
}
