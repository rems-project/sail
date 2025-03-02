default Order dec

$include <prelude.sail>

val example : unit -> unit

function example() = {
  let some_vector : vector(5, int) = config some.json_list;

  // We can also read the configuration value into a Sail list
  let some_list : list(int) = config some.json_list;
}
