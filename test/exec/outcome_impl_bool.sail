default Order dec

$include <prelude.sail>

$target_set emulator c cpp ocaml interpreter systemverilog

outcome foo : bits(if 'is_32 then 32 else 64) -> unit with 'is_32 = {
  impl emulator(bv) = {
    if constraint('is_32) then {
      print_endline("32")
    } else {
      print_endline("64")
    }
  }
}

instantiation foo with 'is_32 = true

val main : unit -> unit

function main() = {
  foo(0x0000_0000)
}
