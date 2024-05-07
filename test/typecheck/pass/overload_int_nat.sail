default Order dec

$include <prelude.sail>

val f : int -> int

val g : string -> string

overload h = {f, g}

val main : unit -> unit

function main() = {
  let x : nat = 3;
  let _ = h(x);
}
