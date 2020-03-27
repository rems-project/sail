$include <flow.sail>

val main : unit -> unit

function main() = {
  repeat {
    _prove(constraint(false));
  } until (false);
}
