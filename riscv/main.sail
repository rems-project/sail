val fetch_and_execute : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

val elf_tohost = {
  ocaml: "Elf_loader.elf_tohost",
  c: "elf_tohost"
} :  unit -> int

val loop : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}
function loop () = {
  let tohost = __GetSlice_int(64, elf_tohost(), 0);
  i : int = 0;
  while true do {
    tick_clock();
    print_int("\nstep: ", i);
    let retired : bool = step();
    PC = nextPC;
    if retired then i = i + 1;

    /* check htif exit */
    let tohost_val = __ReadRAM(64, 4, 0x0000_0000_0000_0000, tohost);
    if unsigned(tohost_val) != 0 then {
      let exit_val = unsigned(tohost_val >> 0b1) in
      if exit_val == 0 then
        print("SUCCESS")
      else
        print_int("FAILURE: ", exit_val);
      exit(());
    }
  }
}

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  c: "elf_entry"
} : unit -> int

val main : unit -> unit effect pure //{barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function main () = {

  print(assembly(ITYPE(0b000000000000, 0b00000, 0b11010, RISCV_ADDI)));
  print(assembly(assembly("addi zero, zero, 0x0")));
  print(assembly(assembly("ldu.aq zero, zero, 0x0")));
  print_bits("assembled lui zero, 0x0: ", encdec(assembly("lui zero, 0x0")));
  print_bits("assembled jal zero, 0x123456 : ", encdec(assembly("jal zero, 0x123456")));
  print(assembly(assembly("beq zero, zero, 0x124")));
  print_bits("assembled beq zero, zero, 0x124 : ", encdec(assembly("beq zero, zero, 0x124")));
  /*PC = __GetSlice_int(64, elf_entry(), 0);
  try {
    init_sys ();
    loop ()
  } catch {
    Error_not_implemented(s) => print_string("Error: Not implemented: ", s),
    Error_EBREAK() => print("EBREAK"),
    Error_internal_error() => print("Error: internal error")
  }*/
}
