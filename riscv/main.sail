val fetch_and_execute : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

val elf_tohost = {
  ocaml: "Elf_loader.elf_tohost",
  c: "elf_tohost"
} :  unit -> int

function fetch_and_execute () =
  let tohost = __GetSlice_int(64, elf_tohost(), 0) in
  while true do {
    print_bits("\nPC: ", PC);

    /* for now, always fetch a 32-bit value.  this would need to
       change with privileged mode, since we could cross a page
       boundary with PC only 16-bit aligned in C mode.  */
    let instr = __RISCV_read(PC, 4);

    let (instr_ast, instr_sz) : (option(ast), int)=
       match (instr[1 .. 0]) {
         0b11 => (decode(instr), 4),
	 _    => (decodeCompressed(instr[15 .. 0]), 2)
       };
    match (instr_ast, instr_sz) {
      (Some(ast), 4) => print(BitStr(instr)          ^ ":  " ^ ast),
      (Some(ast), 2) => print(BitStr(instr[15 .. 0]) ^ ":  " ^ ast),
      (_,         _) => print(BitStr(instr)          ^ ":  no-decode")
    };
    /* check whether a compressed instruction is legal. */
    if (misa.C() == 0b0 & (instr_sz == 2)) then {
      let t : sync_exception =
      struct { trap = E_Illegal_Instr,
               excinfo = Some (EXTZ(instr)) } in
      nextPC = handle_exception_ctl(cur_privilege, CTL_TRAP(t), PC)
    } else {
      nextPC = PC + instr_sz;
      match instr_ast {
        Some(ast) => execute(ast),
	None()    => {print("Decode failed"); exit()}
      }
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

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  c: "elf_entry"
} : unit -> int

val main : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function dump_state () : unit -> unit = {
  print("Dumping state");
  print_bits(" PC: ", PC);
  let instr = __RISCV_read(PC, 4);
  print_bits(" instr: ", instr)
}

function main () = {
  PC = __GetSlice_int(64, elf_entry(), 0);
  try {
    init_sys ();
    fetch_and_execute()
  } catch {
    Error_not_implemented(s) => print_string("Error: Not implemented: ", s),
    Error_misaligned_access() => print("Error: misaligned_access"),
    Error_EBREAK() => print("EBREAK"),
    Error_internal_error() => print("Error: internal error")
  };
  dump_state ()
}
