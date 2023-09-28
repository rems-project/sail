$include <prelude.sail>

val main : unit -> unit

function main() = {
  foreach (i from 0 to -1 by 1 in inc) {
    print("unreachable\n");
  };
  print("ok\n")
}
