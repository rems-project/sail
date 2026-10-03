default Order dec

$include <option.sail>
$include <generic_equality.sail>
$include <string.sail>

val main : unit -> unit

function main() = {
  let x : option(int) = Some(3);
  let y : option(int) = Some(4);
  let z : option(int) = None();
  assert(x != y);
  assert(x != None());
  assert(x == Some(3));
  assert(z == None());
  assert(z == z);
  assert(x == x);
  print_endline("ok")
}
