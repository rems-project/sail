$include <elf.sail>

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function fetch_and_execute () =
  while true do {
    try {
      let instr = aget_Mem(_PC, 4, AccType_IFETCH);
      decode(instr);
    } catch {
      Error_See(h) if h == "HINT" => (),
      _ => exit(())
    };
    if __BranchTaken then __BranchTaken = false else _PC = _PC + 4
  }

val main : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function main () = {
  _PC = __GetSlice_int(64, elf_entry(), 0);
  SP_EL0 = ZeroExtend(0x3C00, 64);
  PSTATE.D = 0b1;
  PSTATE.A = 0b1;
  PSTATE.I = 0b1;
  PSTATE.F = 0b1;
  OSLSR_EL1 = ZeroExtend(0b10, 32);
  __BranchTaken = false;
  fetch_and_execute()
}
