default Order dec

$include <prelude.sail>
$include <elf.sail>

// Test for the elf_tohost primitive
function main() -> unit = {
  assert(elf_tohost() == 0);
}
