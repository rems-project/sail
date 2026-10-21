default Order dec

$include <prelude.sail>

register R1 : bits(if 32 == 64 then 8 else 16)

register R2 : bits(if 32 != 64 then 8 else 16)

val main : unit -> unit

function main() = {
  print_endline("ok")
}
