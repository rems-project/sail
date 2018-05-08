$ifndef _ELF
$define _ELF

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  lem: "elf_entry",
  c: "elf_entry"
} : unit -> int

val elf_tohost = {
  ocaml: "Elf_loader.elf_tohost",
  lem: "elf_tohost",
  c: "elf_tohost"
} : unit -> int

$endif
