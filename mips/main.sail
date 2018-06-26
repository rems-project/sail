
val cycle_count = { c: "cycle_count" } : unit -> unit

function cycle_count() = ()

register instCount : int

val fetch_and_execute : unit -> bool effect {barr, eamem, escape, rmem, rreg, wmv, wreg, undef, wmvt, rmemt}
function fetch_and_execute () = {
  PC = nextPC;
  inBranchDelay = branchPending;
  branchPending = 0b0;
  nextPC = if inBranchDelay then delayedPC else PC + 4;
  cp2_next_pc();
  instCount = instCount + 1;
  if UART_WRITTEN then {
    putchar(unsigned(UART_WDATA));
    UART_WRITTEN = 0b0;
  };
  /* the following skips are required on mips to fake the tag effects otherwise type checker complains  */
  skip_rmemt();
  skip_wmvt();
  /* prerr_bits("PC: ", PC); */
  loop_again = true;
  try {
    let pc_pa = TranslatePC(PC);
    /*print_bits("pa: ", pc_pa);*/
    let instr = MEMr_wrapper(pc_pa, 4);
    /*print_bits("hex: ", instr);*/
    let instr_ast = decode(instr);
    match instr_ast {
      Some(HCF()) => {
                     print("simulation stopped due to halt instruction.");
                     loop_again = false
                   },
      Some(ast) => execute(ast),
      None()    => { print("Decode failed"); loop_again=false } /* Never expect this -- unknown instruction should actually result in reserved instruction ISA-level exception (see mips_ri.sail). */
    }
  } catch {
    ISAException() => () /*prerr_endline("EXCEPTION")*/
    /* ISA-level exception occurrred either during TranslatePC or execute --
       just continue from nextPC, which should have been set to the appropriate
       exception vector (along with clearing branchPending etc.) . */
  };
  cycle_count();
  loop_again;
}

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  lem: "elf_entry",
  c: "elf_entry"
} : unit -> int

val init_registers : bits(64) -> unit effect {wreg}

function init_registers (initialPC) = {
  init_cp0_state();
  init_cp2_state();
  nextPC = initialPC;
}

function dump_mips_state () : unit -> unit = {
  print_bits("DEBUG MIPS PC ", PC);
  foreach (idx from 0 to 31) {
    print(concat_str("DEBUG MIPS REG ", concat_str(string_of_int(idx), concat_str(" ", BitStr(rGPR(to_bits(5,idx)))))));
  }
}

val main : unit -> unit effect {barr, eamem, escape, rmem, rreg, undef, wmv, wreg, rmemt, wmvt}

function main () = {
  init_registers(to_bits(64, elf_entry()));
  startTime = get_time_ns();
  while (fetch_and_execute()) do {
    /* uncomment to print IPS every 10M instructions (~10s)
    if (instCount == 10000000) then {
      endTime = get_time_ns();
      elapsed = endTime - startTime;
      inst_1e9 = instCount * 1000000000;
      ips = inst_1e9 / elapsed;
      print_int("*IPS*: ", ips);
      startTime = get_time_ns();
      instCount = 0; 
    };*/
    ();
  };

  endTime = get_time_ns();
  elapsed = endTime - startTime;
  inst_1e9 = instCount * 1000000000;
  ips = inst_1e9 / elapsed;
  dump_mips_state ();
  dump_cp2_state ();
  print_int("Executed instructions: ", instCount);
  print_int("Nanoseconds elapsed: ", elapsed);
  print_int("Instructions per second: ", ips);
}
