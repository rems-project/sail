/* Platform and devices */

/* Current constraints on this implementation are:
   - it cannot access memory directly, but instead provides definitions for the physical memory model
   - it can access system register state, needed to manipulate interrupt bits
   - it relies on externs to get platform address information and doesn't hardcode them.
*/

/* Main memory */
val plat_ram_base = {ocaml: "Platform.dram_base", lem: "plat_ram_base"} : unit -> xlenbits
val plat_ram_size = {ocaml: "Platform.dram_size", lem: "plat_ram_size"} : unit -> xlenbits

/* ROM holding reset vector and device-tree DTB */
val plat_rom_base = {ocaml: "Platform.rom_base", lem: "plat_rom_base"} : unit -> xlenbits
val plat_rom_size = {ocaml: "Platform.rom_size", lem: "plat_rom_size"} : unit -> xlenbits

/* Location of clock-interface, which should match with the spec in the DTB */
val plat_clint_base = {ocaml: "Platform.clint_base", lem: "plat_clint_base"} : unit -> xlenbits
val plat_clint_size = {ocaml: "Platform.clint_size", lem: "plat_clint_size"} : unit -> xlenbits

val phys_mem_segments : unit -> (xlenbits, xlenbits)
function phys_mem_segments() =
// FIXME
// (plat_rom_base (), plat_rom_size ()) ::
  (plat_ram_base (), plat_ram_size ())
// :: [||]

val plat_insns_per_tick = {ocaml: "Platform.insns_per_tick"} : unit -> int

/* CLINT clock device interface, based on Spike. */

// assumes a single hart, since this typically is a vector of per-hart registers.
register mtimecmp : xlenbits  // memory-mapped internal clint register.

/* CLINT memory-mapped IO */

let MSIP_BASE     : xlenbits = 0x0000000000000000
let MTIMECMP_BASE : xlenbits = 0x0000000000004000
let MTIME_BASE    : xlenbits = 0x000000000000bff8

/* 0000 msip hart 0
 * 0004 msip hart 1
 * 4000 mtimecmp hart 0 lo
 * 4004 mtimecmp hart 0 hi
 * 4008 mtimecmp hart 1 lo
 * 400c mtimecmp hart 1 hi
 * bff8 mtime lo
 * bffc mtime hi
 */

val clint_load : forall 'n, 'n > 0. (xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rreg}
function clint_load(addr, width) = {
  /* FIXME: For now, only allow exact aligned access.
     I couldn't make the more general access pass the type-checker.
   */
  if addr == MSIP_BASE & ('n == 8 | 'n == 4)
  then MemValue(zero_extend(mip.MSI(), sizeof(8 * 'n)))
  /* FIXME:
  else if addr == MTIMECMP_BASE & ('n == 8)
  then MemValue(mtimecmp)
  */
  /* FIXME:
  else if addr == MTIME_BASE & ('n == 8)
  then MemValue(mtime)
  */
  else MemException(E_Load_Access_Fault)
}

val clint_store: forall 'n, 'n > 0. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wreg}
function clint_store(addr, width, data) = {
  if addr == MSIP_BASE & ('n == 8 | 'n == 4) then {
    mip->MSI() = data[0] == 0b1;
    MemValue(())
  } else if addr == MTIMECMP_BASE & 'n == 8 then {
    /* FIXME:
    mtimecmp = data;
    */
    MemValue(())
  } else MemException(E_SAMO_Access_Fault)
}

/* Spike's HTIF device interface. */

bitfield htif_cmd : bits(64) = {
  device  : 63 .. 56,
  cmd     : 55 .. 48,
  payload : 47 .. 0
}

// no support yet for terminal input
val htif_load : forall 'n, 'n > 0. (xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n))
function htif_load(addr, width) = MemValue(EXTZ(0b0))

val htif_store: forall 'n, 'n > 0. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(unit)
function htif_store(addr, width, data) = {
  // since htif is only available at a single address, we'll assume here that physical memory
  // model has correctly dispatched the address.
  let cbits : xlenbits = /* if 'n == 4 then EXTZ(data) else data */ EXTZ(0b0);
  let cmd = Mk_htif_cmd(cbits);
  match cmd.device() {
    0x00 => { /* syscall-proxy */
      if cmd.payload()[0] == 0b1
      then /* TODO: exit command
            * for e.g. set a flag that's checked by the top-level loop.
            * but that might appear to be a register write effect triggered by a memory write.
            */
           ()
      else ()
    },
    0x01 => { /* terminal */
      match cmd.cmd() {
        0x00 => /* input */ (),
        0x01 => /* TODO: output data */ (),
        c    => print("Unknown term cmd: " ^ BitStr(c))
      }
    },
    d => print("Unknown htif device:" ^ BitStr(d))
  };
  MemValue(())
}
