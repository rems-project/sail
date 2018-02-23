default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
val eq_int = {ocaml: "eq_int", lem: "eq"} : (int, int) -> bool
overload operator == = {eq_int, eq_vec}
val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))


/* Check case splitting on a vector */

val test : bits(32) -> nat

function test((sel : bits(2)) @ (_ : bits(30))) = {
  match (sel) {
    0b00 => 5,
    0b10 => 1,
    _ => 0
  }
}

val run : unit -> unit effect {escape}

function run () = {
  assert(test(0x0f353533) == 5);
  assert(test(0x84534656) == 1);
  assert(test(0xf3463903) == 0);
}
