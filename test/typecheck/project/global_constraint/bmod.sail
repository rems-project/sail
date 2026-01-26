
val main : unit -> unit

function main() = {
  let 'x = 3;
  _prove(constraint('x <= 32));
}
