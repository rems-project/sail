default Order dec

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (vector('n, dec, bit), atom('m), atom('o)) -> vector('m - ('o - 1), dec, bit)

val test : vector(4, dec, bit) -> unit

function test nzcv = {
  N = 0b0;
  Z = 0b0;
  C = 0b0;
  V = 0b0;
  (N @ Z @ C @ V) = nzcv;
  ()
}
