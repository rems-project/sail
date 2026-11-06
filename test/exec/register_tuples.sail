default Order dec
$include <prelude.sail>

register x : option((bool, int)) = None()

struct sty = {
  fld: (bool, int),
}

register y : sty = struct { fld = (false, 0) }

register z : (bool, (bool, int)) = (false, (false, 0))

function main() -> unit = {
  x = Some((true, 5));
  y = struct { fld = (true, 2) };
  z = (true, (true, 3));
  match x {
    None() => assert(false),
    Some((b, i)) => {
      assert(b);
      assert(i == 5);
    }
  };
  let (a,b) = y.fld;
  assert(a & b == 2);
  let (c,(d,e)) = z;
  assert(c & d & e == 3);
}
