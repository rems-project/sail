default Order dec

$include <vector_dec.sail>

val main : unit -> unit

function main () = {
  x : int = 3;
  return ();
  x = x;
  ()
}