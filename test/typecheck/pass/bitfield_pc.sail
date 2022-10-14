default Order dec

$include <vector_dec.sail>

bitfield PC_t : bitvector(16, dec) = {
  H : 15 .. 8,
  L :  7 .. 0
}

let zero_PC : PC_t = Mk_PC_t(sail_zeros(16))

val inc_PC_L : PC_t -> PC_t

function inc_PC_L (pc) =
  let l = pc[L] in
  [pc with L = (l + 1)]

val init_PC : (bits(8), bits(8)) -> PC_t

function init_PC (h, l) = [zero_PC with H = h, L = l]

val main : unit -> unit

function main () = {
  let pc = inc_PC_L(zero_PC);
  print_bits("PC=", pc.bits);
  print_bits("init_PC(0x47, 0x11)=", init_PC(0x47, 0x11).bits)
}
