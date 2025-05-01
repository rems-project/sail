default Order dec

$include <prelude.sail>

$target_set emulator c ocaml interpreter systemverilog

outcome foo : bits('n) -> unit with 'n, constraint 'n in {32, 64} = {
  impl emulator(bv) = {
    if sizeof('n) == 32 then {
      print_endline("32")
    } else {
      _prove(constraint('n == 64));
      print_endline("64")
    }
  }
}

instantiation foo with 'n = 32

val main : unit -> unit

function main() = {
  foo(0x0000_0000)
}
