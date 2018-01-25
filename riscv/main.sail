val fetch_and_execute : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function break () : unit -> unit = ()

function fetch_and_execute () = while true do {
  let instr = __RISCV_read(PC, 4);
  nextPC = PC + 4;
  let instr_ast = decode(instr);
  break ();
  match instr_ast {
    Some(ast) => execute(ast),
    None      => exit (())
  };
  PC = nextPC
}

val elf_entry = "Elf_loader.elf_entry" : unit -> int

val main : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function main () = {
  PC = __GetSlice_int(64, elf_entry(), 0);
  fetch_and_execute()
}
