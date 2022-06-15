default Order dec
$include <prelude.sail>

val f : forall 'a 'b 'c 'n, 0 < 'a & 0 < 'b & 0 < 'c & 'a + 'b + 'c == 'n. (implicit('a), implicit('b), implicit('c), bits('n)) -> (bits('a), bits('b), bits('c))

function f(a,b,c,v) = {
  x : bits('a) = undefined;
  y : bits('b) = undefined;
  z : bits('c) = undefined;
  (x @ y @ z) = v;
  (x,y,z)
}
