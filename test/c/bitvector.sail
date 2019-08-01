default Order dec

$include <vector_dec.sail>

val test : (bitvector(16, dec), bitvector(200, dec)) -> bool

function test (x, y)  = {
  print_bits("x = ", x);
  print_bits("y = ", y);
  true
}

val main : unit -> unit

function main () = {
  if test(0xBEEF, sail_zeros(200)) then () else ();
  let z = 0xCAFE;
  print_bits("z = ", z);
  print_bits("zero_extend(z) = ", sail_zero_extend(z, 32));
  let q = 0xAB_FEED_DEAD_BEEF_CAFE;
  print_bits("q = ", q);
  let k = 0xFF;
  print_bits("k = ", k);
  print_bits("k + k = ", add_bits(k, k));
  print_bits("0xFF + 1 = ", add_bits_int(0xFF, 1));
  print_bits("0xFF + 2 = ", add_bits_int(0xFF, 2));
  print_bits("0xFF + 3 = ", add_bits_int(0xFF, 3));
  ()
}
