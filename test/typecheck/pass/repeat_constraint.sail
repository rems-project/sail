$include <flow.sail>

val main : unit -> unit

function main() = {
  repeat {
    _not_prove(constraint(false));
  } until (false);
}
