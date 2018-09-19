/* Platform-specific definitions, and basic MMIO devices. */

/* Current constraints on this implementation are:
   - it cannot access memory directly, but instead provides definitions for the physical memory model
   - it can access system register state, needed to manipulate interrupt bits
   - it relies on externs to get platform address information and doesn't hardcode them.
*/

/* Main memory */
val plat_ram_base = {c: "plat_ram_base", ocaml: "Platform.dram_base", lem: "plat_ram_base"} : unit -> xlenbits
val plat_ram_size = {c: "plat_ram_size", ocaml: "Platform.dram_size", lem: "plat_ram_size"} : unit -> xlenbits

/* whether the MMU should update dirty bits in PTEs */
val plat_enable_dirty_update = {ocaml: "Platform.enable_dirty_update",
                                c: "plat_enable_dirty_update",
                                lem: "plat_enable_dirty_update"} : unit -> bool

/* whether the platform supports misaligned accesses without trapping to M-mode. if false,
 * misaligned loads/stores are trapped to Machine mode.
 */
val plat_enable_misaligned_access = {ocaml: "Platform.enable_misaligned_access",
                                     c: "plat_enable_misaligned_access",
                                     lem: "plat_enable_misaligned_access"} : unit -> bool

/* ROM holding reset vector and device-tree DTB */
val plat_rom_base   = {ocaml: "Platform.rom_base", c: "plat_rom_base", lem: "plat_rom_base"} : unit -> xlenbits
val plat_rom_size   = {ocaml: "Platform.rom_size", c: "plat_rom_size", lem: "plat_rom_size"} : unit -> xlenbits

/* Location of clock-interface, which should match with the spec in the DTB */
val plat_clint_base = {ocaml: "Platform.clint_base", c: "plat_clint_base", lem: "plat_clint_base"} : unit -> xlenbits
val plat_clint_size = {ocaml: "Platform.clint_size", c: "plat_clint_size", lem: "plat_clint_size"} : unit -> xlenbits

/* Location of HTIF ports */
val plat_htif_tohost = {ocaml: "Platform.htif_tohost", c: "plat_htif_tohost", lem: "plat_htif_tohost"} : unit -> xlenbits
// todo: fromhost

val phys_mem_segments : unit -> list((xlenbits, xlenbits))
function phys_mem_segments() =
  (plat_rom_base (), plat_rom_size ()) ::
  (plat_ram_base (), plat_ram_size ()) ::
  [||]

/* Physical memory map predicates */

function within_phys_mem(addr : xlenbits, width : atom('n)) -> forall 'n. bool = {
  let ram_base = plat_ram_base ();
  let rom_base = plat_rom_base ();
  let ram_size = plat_ram_size ();
  let rom_size = plat_rom_size ();

  /* todo: iterate over segment list */
  if (  ram_base <=_u addr
      & (addr + sizeof('n)) <=_u (ram_base + ram_size))
       then true
  else if (  rom_base <=_u addr
           & (addr + sizeof('n)) <=_u (rom_base + rom_size))
       then true
  else {
    print("within_phys_mem: " ^ BitStr(addr) ^ " not within phys-mem:");
    print("  plat_rom_base: " ^ BitStr(rom_base));
    print("  plat_rom_size: " ^ BitStr(rom_size));
    print("  plat_ram_base: " ^ BitStr(ram_base));
    print("  plat_ram_size: " ^ BitStr(ram_size));
    false
  }
}

function within_clint(addr : xlenbits, width : atom('n)) -> forall 'n. bool =
    plat_clint_base() <=_u addr
  & (addr + sizeof('n)) <=_u (plat_clint_base() + plat_clint_size())

function within_htif_writable(addr : xlenbits, width : atom('n)) -> forall 'n. bool =
    plat_htif_tohost() == addr

function within_htif_readable(addr : xlenbits, width : atom('n)) -> forall 'n. bool =
    plat_htif_tohost() == addr

/* CLINT (Core Local Interruptor), based on Spike. */

val plat_insns_per_tick = {ocaml: "Platform.insns_per_tick", c: "plat_insns_per_tick", lem: "plat_insns_per_tick"} : unit -> int

// assumes a single hart, since this typically is a vector of per-hart registers.
register mtimecmp : xlenbits  // memory-mapped internal clint register.

/* CLINT memory-mapped IO */

/* relative address map:
 *
 * 0000 msip hart 0         -- memory-mapped software interrupt
 * 0004 msip hart 1
 * 4000 mtimecmp hart 0 lo  -- memory-mapped timer thresholds
 * 4004 mtimecmp hart 0 hi
 * 4008 mtimecmp hart 1 lo
 * 400c mtimecmp hart 1 hi
 * bff8 mtime lo            -- memory-mapped clocktimer value
 * bffc mtime hi
 */

let MSIP_BASE     : xlenbits = 0x0000000000000000
let MTIMECMP_BASE : xlenbits = 0x0000000000004000
let MTIME_BASE    : xlenbits = 0x000000000000bff8

val clint_load : forall 'n, 'n > 0. (xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rreg}
function clint_load(addr, width) = {
  let addr = addr - plat_clint_base ();
  /* FIXME: For now, only allow exact aligned access. */
  if addr == MSIP_BASE & ('n == 8 | 'n == 4)
  then {
    print("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mip.MSI()));
    MemValue(zero_extend_type_hack(mip.MSI(), sizeof(8 * 'n)))
  }
  else if addr == MTIMECMP_BASE & ('n == 8)
  then {
    print("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtimecmp));
    MemValue(zero_extend_type_hack(mtimecmp, 64)) /* FIXME: Redundant zero_extend currently required by Lem backend */
  }
  else if addr == MTIME_BASE & ('n == 8)
  then {
    print("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtime));
    MemValue(zero_extend_type_hack(mtime, 64))
  }
  else {
    print("clint[" ^ BitStr(addr) ^ "] -> <not-mapped>");
    MemException(E_Load_Access_Fault)
  }
}

function clint_dispatch() -> unit = {
  print("clint::tick mtime <- " ^ BitStr(mtime));
  mip->MTI() = false;
  if mtimecmp <=_u mtime then {
    print(" clint timer pending at mtime " ^ BitStr(mtime));
    mip->MTI() = true
  }
}

/* The rreg effect is due to checking mtime. */
val clint_store: forall 'n, 'n > 0. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {rreg,wreg}
function clint_store(addr, width, data) = {
  let addr = addr - plat_clint_base ();
  if addr == MSIP_BASE & ('n == 8 | 'n == 4) then {
    print("clint[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (mip.MSI <- " ^ BitStr(data[0]) ^ ")");
    mip->MSI() = data[0] == 0b1;
    clint_dispatch();
    MemValue(true)
  } else if addr == MTIMECMP_BASE & 'n == 8 then {
    print("clint[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (mtimecmp)");
    mtimecmp = zero_extend(data, 64); /* FIXME: Redundant zero_extend currently required by Lem backend */
    clint_dispatch();
    MemValue(true)
  } else {
    print("clint[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (<unmapped>)");
    MemException(E_SAMO_Access_Fault)
  }
}

val tick_clock : unit -> unit effect {rreg, wreg}
function tick_clock() = {
  mcycle = mcycle + 1;
  mtime  = mtime  + 1;
  clint_dispatch()
}

/* Basic terminal character I/O. */

val plat_term_write = {ocaml: "Platform.term_write", c: "plat_term_write", lem: "plat_term_write"} : bits(8) -> unit
val plat_term_read  = {ocaml: "Platform.term_read",  c: "plat_term_read", lem: "plat_term_read"}  : unit -> bits(8)

/* Spike's HTIF device interface, which multiplexes the above MMIO devices. */

bitfield htif_cmd : bits(64) = {
  device  : 63 .. 56,
  cmd     : 55 .. 48,
  payload : 47 .. 0
}

register htif_tohost : xlenbits
register htif_done   : bool
register htif_exit_code : xlenbits


/* Since the htif tohost port is only available at a single address,
 * we'll assume here that physical memory model has correctly
 * dispatched the address.
 */

val htif_load : forall 'n, 'n > 0. (xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rreg}
function htif_load(addr, width) = {
  print("htif[" ^ BitStr(addr) ^ "] -> " ^ BitStr(htif_tohost));
  /* FIXME: For now, only allow the expected access widths. */
  if width == 8
  then MemValue(zero_extend_type_hack(htif_tohost, 64))  /* FIXME: Redundant zero_extend currently required by Lem backend */
  else MemException(E_Load_Access_Fault)
}

/* The wreg effect is an artifact of using 'register' to implement device state. */
val htif_store: forall 'n, 0 < 'n <= 8. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wreg}
function htif_store(addr, width, data) = {
  print("htif[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data));
  /* Store the written value so that we can ack it later. */
  let cbits : xlenbits = EXTZ(data);
  htif_tohost = cbits;
  /* Process the cmd immediately; this is needed for terminal output. */
  let cmd = Mk_htif_cmd(cbits);
  match cmd.device() {
    0x00 => { /* syscall-proxy */
      print("htif-syscall-proxy cmd: " ^ BitStr(cmd.payload()));
      if cmd.payload()[0] == 0b1
      then {
           htif_done = true;
           htif_exit_code = (zero_extend(cmd.payload(), xlen) >> 0b01) : xlenbits
      }
      else ()
    },
    0x01 => { /* terminal */
      print("htif-term cmd: " ^ BitStr(cmd.payload()));
      match cmd.cmd() {
        0x00 => /* TODO: terminal input handling */ (),
        0x01 => plat_term_write(cmd.payload()[7..0]),
        c    => print("Unknown term cmd: " ^ BitStr(c))
      }
    },
    d => print("htif-???? cmd: " ^ BitStr(data))
  };
  MemValue(true)
}

val htif_tick : unit -> unit effect {rreg, wreg}
function htif_tick() = {
  print("htif::tick " ^ BitStr(htif_tohost));
  htif_tohost = EXTZ(0b0)  /* htif ack */
}

/* Top-level MMIO dispatch */

function within_mmio_readable(addr : xlenbits, width : atom('n)) -> forall 'n. bool =
  within_clint(addr, width) | (within_htif_readable(addr, width) & 1 <= 'n)

function within_mmio_writable(addr : xlenbits, width : atom('n)) -> forall 'n. bool =
  within_clint(addr, width) | (within_htif_writable(addr, width) & 'n <= 8)

function mmio_read(addr : xlenbits, width : atom('n)) -> forall 'n, 'n > 0. MemoryOpResult(bits(8 * 'n)) =
  if   within_clint(addr, width)
  then clint_load(addr, width)
  else if within_htif_readable(addr, width) & (1 <= 'n)
  then htif_load(addr, width)
  else MemException(E_Load_Access_Fault)

function mmio_write(addr : xlenbits, width : atom('n), data: bits(8 * 'n)) -> forall 'n, 'n > 0. MemoryOpResult(bool) =
  if   within_clint(addr, width)
  then clint_store(addr, width, data)
  else if within_htif_writable(addr, width) & 'n <= 8
  then htif_store(addr, width, data)
  else MemException(E_SAMO_Access_Fault)

/* Platform initialization and ticking. */

function init_platform() -> unit = {
  htif_tohost = EXTZ(0b0);
  htif_done   = false;
  htif_exit_code = EXTZ(0b0)
}

function tick_platform() -> unit = {
  cancel_reservation();
  htif_tick();
}
