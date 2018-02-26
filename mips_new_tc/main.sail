


val fetch_and_execute : unit -> unit effect {barr, eamem, escape, rmem, rreg, wmv, wreg, undef}
function fetch_and_execute () = {
  while true do {
    PC = nextPC;
    inBranchDelay = branchPending;
    branchPending = 0b0;
    nextPC = if inBranchDelay then delayedPC else PC + 4;

    print_bits("PC: ", PC);
    try {
      let pc_pa = TranslatePC(PC);
      /*print_bits("pa: ", pc_pa);*/
      let instr = MEMr_wrapper(pc_pa, 4);
      /*print_bits("hex: ", instr);*/
      let instr_ast = decode(instr);
      match instr_ast {
        Some(HCF) => {
                       print("simulation stopped due to halt instruction.");
                       return ();
                     },
        Some(ast) => execute(ast),
        None      => {print("Decode failed"); exit (())} /* Never expect this -- unknown instruction should actually result in reserved instruction ISA-level exception (see mips_ri.sail). */
      }
    } catch {
      ISAException => print("EXCEPTION")
      /* ISA-level exception occurrred either during TranslatePC or execute --
         just continue from nextPC, which should have been set to the appropriate
         exception vector (along with clearing branchPending etc.) . */
    };
  }
}

val elf_entry = "Elf_loader.elf_entry" : unit -> int

val main : unit -> unit effect {barr, eamem, escape, rmem, rreg, undef, wmv, wreg}

function dump_state () : unit -> unit = {
  print_bits("DEBUG MIPS PC ", PC);
  foreach (idx from 0 to 32) {
    print(concat_str("DEBUG MIPS REG ", concat_str(string_of_int(idx), concat_str(" ", BitStr(rGPR(to_bits(5,idx)))))));
  }
}

function main () = {
  nextPC = to_bits(64, elf_entry());
  CP0Status->BEV() = bitone;
  fetch_and_execute();
  dump_state ()
}
