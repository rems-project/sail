default Order dec

$include <prelude.sail>
$include <mapping.sail>
$include <string.sail>

overload operator ^ = {concat_str}

union instruction = {
  FENCE : bits(4)
}

mapping fence_bits : bits(4) <-> string = {
  0b0000 <-> "0",
}

mapping assembly : instruction <-> string = {
  backwards "fence" ^ fence_bits(pred) => FENCE(pred),
  forwards FENCE(pred) => "fence" ^ fence_bits(pred)
}

function print_insn(insn : instruction) -> string = assembly(insn)

function main() -> unit = {
  let insn : instruction = FENCE(0b0000);
  print_endline(print_insn(insn))
}
