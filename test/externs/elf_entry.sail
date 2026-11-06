default Order dec

$include <prelude.sail>
$include <elf.sail>

// Test for the elf_entry primitive
function main() -> unit = {
  assert(elf_entry() == 0);
}
