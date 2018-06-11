
val "print_int" : (string, int) -> unit

function main(() : unit) -> unit = {
  let i : int = undefined;
  foreach (i from 0 to 3) {
    print_int("i = ", i);
  }
}