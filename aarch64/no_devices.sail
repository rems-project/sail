
val ___WriteRAM = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> bool effect {wmem}

val __InitRAM : forall 'm. (atom('m), int, bits('m), bits(8)) -> unit

function __InitRAM (_, _, _, _) = ()

val ___ReadRAM = "read_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

val __ReadRAM : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

function __ReadRAM(addr_length, bytes, hex_ram, addr) =
{
  ___ReadRAM(addr_length, bytes, hex_ram, addr)
}

val __TraceMemoryWrite : forall 'n 'm.
  (atom('n), bits('m), bits(8 * 'n)) -> unit

val __WriteRAM : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit effect {wmem}

function __WriteRAM(addr_length, bytes, hex_ram, addr, data) =
{
  let _ = ___WriteRAM(addr_length, bytes, hex_ram, addr, data) in ()
}

function __TraceMemoryWrite(bytes, addr, data) = ()

val __TraceMemoryRead : forall 'n 'm. (atom('n), bits('m), bits(8 * 'n)) -> unit

function __TraceMemoryRead(bytes, addr, data) = ()