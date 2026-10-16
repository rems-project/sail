default Order dec

$include <prelude.sail>

$option --config fail/config_constraint_violated.json

type xlen : Int = config arch.xlen

constraint xlen in {32, 64}

type maskmax : Int = config arch.maskmax

constraint 0 < maskmax < xlen

val main : unit -> unit

function main() = {
  let _ : nat = config arch.frequency;
  print_int("maskmax = ", sizeof(maskmax))
}
