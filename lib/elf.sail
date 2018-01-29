$ifndef _ELF
$define _ELF

val elf_entry = "Elf_loader.elf_entry" : unit -> int

val elf_tohost = "Elf_loader.elf_tohost" : unit -> int

$endif
