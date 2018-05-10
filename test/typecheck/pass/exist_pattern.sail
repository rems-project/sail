default Order inc

infix 4 ==

register n : nat

register x : nat

register y : nat

val eq_int = {lem: "eq", coq: "Z.eqb"} : (int, int) -> bool
val eq_vec = {lem: "eq_vec", coq: "eq_vec"} : forall ('n : Int). (vector('n, inc, bit), vector('n, inc, bit)) -> bool

overload operator == = {eq_int, eq_vec}

val and_bool = {coq: "andb", _: "and_bool"} : (bool, bool) -> bool

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_inc", coq: "subrange_vec_inc"} : forall ('n : Int) ('m : Int) ('o : Int), 'm <= 'o <= 'n.
  (vector('n, inc, bit), atom('m), atom('o)) -> vector('o - ('m - 1), inc, bit)

type wordsize = {'n, 'n in {8, 16, 32}. range(0, 'n)}

let word : wordsize = 8 : range(0, 8)

val main : unit -> int effect {wreg, rreg}

function main () = {
  n = 1;
  y = match n {
    0 => {
      x = 21;
      x
    },
    1 => {
      x = 42;
      x
    },
    z => {
      x = 99;
      x
    }
  };
  match word {
    8  => x = 32,
    16 => x = 64,
    32 => x = 128
  };
  match 0b010101 {
    0b01 @ _ : vector(1, inc, bit) @ 0b101 => n = 42,
    _ => n = 0
  };
  n = 3;
  match n {
    0 => 21,
    1 => 42,
    u => 99
  }
}
