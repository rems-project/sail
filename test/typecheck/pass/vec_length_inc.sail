default Order inc
$include <vector_inc.sail>

function main () : unit -> unit = {
  let x : bits(8) = 0xff;
  let y = x[3];
  let z = [x with 5 = y];
  ()
}
