$include <flow.sail>

default Order dec

type bits ('n : Int) = vector('n, dec, bit)

val eq_anything = "eq" : forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_anything}

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val decode : vector(16, dec, bit) -> unit

scattered function decode

function clause decode 0x00 @ 0b000 @ _ : bits(1) @ 0x0 as op_code =
  if op_code[5 .. 5] == 0b0 then {
    ()
  } else {
    ()
  }

function clause decode 0x00 @ 0b001 @ [b : bit] @ 0x0 =
  if b == bitone then {
    ()
  } else {
    ()
  }

end decode

val decode2 : vector(16, dec, bit) -> unit

function decode2 x =
  match x {
    0x00 @ 0b000 @ [b : bit]  @ 0x0 =>
      if b == bitone then {
        ()
      } else {
        ()
      }
  }
