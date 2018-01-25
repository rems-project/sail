val fetch_and_execute : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function break () : unit -> unit = ()

val elf_tohost = "Elf_loader.elf_tohost" :  unit -> int

function fetch_and_execute () =
  let tohost = __GetSlice_int(64, elf_tohost(), 0) in
  while true do {
  print_bits("PC: ", PC);
  let instr = __RISCV_read(PC, 4);
  nextPC = PC + 4;
  let instr_ast = decode(instr);
  break ();
  match instr_ast {
    Some(ast) => execute(ast),
    None      => {print("Decode failed"); exit (())}
  };
  let tohost_val = __RISCV_read(tohost, 4);
  if unsigned(tohost_val) != 0 then {
    let exit_val = unsigned(tohost_val >> 0b1) in
    if exit_val == 0 then
      print("SUCCESS")
    else
      print_int("FAILURE: ", exit_val);
    exit (());
  };
  PC = nextPC
}

val elf_entry = "Elf_loader.elf_entry" : unit -> int

val main : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function main () = {
  PC = __GetSlice_int(64, elf_entry(), 0);
  fetch_and_execute()
}
