default Order dec

$include <prelude.sail>

type instruction = bits(16)

val list_index : forall('n : Int), ('n >= 1). (list(bits('n)), int) -> bits('n)

function list_index ((instr :: rest), i) = 
  match i {
    0 => instr,
    _ => list_index(rest, i - 1)
  }

val main : unit -> unit

function main () = {
  instrs : list(instruction) = [|0x0001|];
  print_bits("Instr: ", list_index(instrs, 0))
}
