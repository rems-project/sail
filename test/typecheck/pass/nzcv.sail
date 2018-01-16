default Order dec

val test : vector(4, dec, bit) -> unit

function test nzcv = {
  N = 0b0;
  Z = 0b0;
  C = 0b0;
  V = 0b0;
  (N, Z, C, V) = nzcv;
  ()
}
