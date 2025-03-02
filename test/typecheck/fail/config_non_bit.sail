default Order dec

$include <prelude.sail>

$option --config fail/config_non_bit.json

val main : unit -> unit

function main() = {
  let _ : bits(5) = config k
}
