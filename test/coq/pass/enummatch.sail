default Order dec
$include <prelude.sail>

enum choice = A | B | C | D

val f : (choice, bits(64)) -> bits(64)

function f(x,v) = {
  sz : {|8,10,15|} = 10;
  match x {
  A => sz = 15,
  B => sz = 8,
  _ => (),
  };
  let w = v[20 .. sz];
  sail_zero_extend(w, 64)
}
