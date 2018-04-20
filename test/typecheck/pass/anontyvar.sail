$include <smt.sail>
$include <flow.sail>

/* We shouldn't have to annotate 'a with Type */
val id : forall 'a. 'a -> 'a
function id(x) = {
  x
}

val test : unit -> unit

function test() = {
  let x = id(5);
  ()
}
