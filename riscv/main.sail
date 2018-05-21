val elf_tohost = {
  ocaml: "Elf_loader.elf_tohost",
  c: "elf_tohost"
} :  unit -> int

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  c: "elf_entry"
} : unit -> int

val main : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function main () = {
  PC = __GetSlice_int(64, elf_entry(), 0);
  try {
    init_sys ();
    loop (elf_tohost())
  } catch {
    Error_not_implemented(s) => print_string("Error: Not implemented: ", s),
    Error_internal_error() => print("Error: internal error")
  }
}
