$include <prelude.sail>

val test : (range(2,3), range(1,8)) -> {'n, 'n <= 13. atom('n)}

function test(x,y) = {
  let z : range(3,11) = x + y;
  let w : range(-6,2) = x - y;
  z + w
}