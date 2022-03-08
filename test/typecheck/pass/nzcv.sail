default Order dec

val vector_subrange = pure {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bitvector('n, dec), atom('m), atom('o)) -> bitvector('m - ('o - 1), dec)

val test : bitvector(4, dec) -> unit

function test nzcv = {
  N = 0b0;
  Z = 0b0;
  C = 0b0;
  V = 0b0;
  (N @ Z @ C @ V) = nzcv;
  ()
}
