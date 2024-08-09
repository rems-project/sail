default Order dec

$sail_internal

$include <flow.sail>

val print_endline = "print_endline" : string -> unit

union ast = {
  HCF : unit
}

union option ('a : Type) = {
  Some : 'a,
  None : unit
}

val decode : unit -> option(ast)

function decode() = Some(HCF())

val main : unit -> unit

function main() = {
  let instr = decode();
  match instr {
    Some(HCF()) => print_endline("HCF"),
    Some(_) => print_endline("Some(_)"),
    None() => print_endline("None")
  }
}
