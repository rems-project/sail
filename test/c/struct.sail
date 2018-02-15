default Order dec

val "print_bits" : forall 'n. (string, vector('n, dec, bit)) -> unit

struct test = {
  A : vector(4, dec, bit),
  B : vector(2, dec, bit),
}

function main (() : unit) -> unit = {
  x : test = struct { A = 0b1010, B = 0b11 };
  x.A = 0b1000;
  print_bits("x.A = ", x.A);
  x.A = 0b1111;
  print_bits("x.A = ", x.A);
  print_bits("(struct {A = 0b1111, B = 0b11} : test).B = ", (struct {A = 0b1111, B = 0b11} : test).B);
}