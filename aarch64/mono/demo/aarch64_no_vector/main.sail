val fetch_and_execute : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function fetch_and_execute () = while true do {
  let instr = aget_Mem(_PC, 4, AccType_IFETCH);
  decode(instr);
  if __BranchTaken then __BranchTaken = false else _PC = _PC + 4
}

val elf_entry = "Elf_loader.elf_entry" : unit -> int

val main : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function main () = {
  _PC = __GetSlice_int(64, elf_entry(), 0);
  print(BitStr(_PC));
  SP_EL0 = ZeroExtend(0x3C00, 64);
  PSTATE.D = 0b1;
  PSTATE.A = 0b1;
  PSTATE.I = 0b1;
  PSTATE.F = 0b1;
  OSLSR_EL1 = ZeroExtend(0b10, 32);
  __BranchTaken = false;
  fetch_and_execute()
}
