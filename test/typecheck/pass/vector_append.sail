val append = pure {ocaml: "append", lem: "concat_vec"} : forall ('l1 : Int) ('l2 : Int) ('o : Order), 'l1 >= 0 & 'l2 >= 0.
  (vector('l1, 'o, bit), vector('l2, 'o, bit)) -> vector('l1 + 'l2, 'o, bit)

default Order inc

val test : (vector(4, inc, bit), vector(4, inc, bit)) -> vector(8, inc, bit)

function test (v1, v2) = {
  zv = append(v1, v2);
  zv = v1 @ v2;
  zv
}
