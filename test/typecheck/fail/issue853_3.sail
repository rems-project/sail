default Order dec
$include <prelude.sail>

type xlenbits = bits(32)
type physaddrbits = bits(34)

newtype physaddr = physaddr : physaddrbits

function physaddr_bits(physaddr(paddr) : physaddr) -> physaddrbits = paddr

struct Track_MemoryAccess = {
  physical_address : xlenbits,
}

register track_memory_accesses : list(Track_MemoryAccess) = [||]

function track_read(paddr : physaddr) -> unit = {
  track_memory_accesses = struct {
    physical_address = physaddr_bits(paddr),
  } :: track_memory_accesses;
}
