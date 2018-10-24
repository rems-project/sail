/* Physical memory model.
 *
 * This assumes that the platform memory map has been defined, so that accesses
 * to MMIO regions can be dispatched.
 */

function is_aligned_addr (addr : xlenbits, width : atom('n)) -> forall 'n. bool =
  unsigned(addr) % width == 0

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_read(t : ReadType, addr : xlenbits, width : atom('n), aq : bool, rl: bool, res : bool) -> forall 'n, 'n > 0. MemoryOpResult(bits(8 * 'n)) =
  let result : option(bits(8 * 'n)) = match (aq, rl, res) {
    (false, false, false) => Some(__read_mem(Read_plain, addr, width)),
    (true,  false, false) => Some(__read_mem(Read_RISCV_acquire, addr, width)),
    (true,  true,  false) => Some(__read_mem(Read_RISCV_strong_acquire, addr, width)),
    (false, false, true)  => Some(__read_mem(Read_RISCV_reserved, addr, width)),
    (true,  false, true)  => Some(__read_mem(Read_RISCV_reserved_acquire, addr, width)),
    (true,  true,  true)  => Some(__read_mem(Read_RISCV_reserved_strong_acquire, addr, width)),
    (false, true,  false) => None(),
    (false, true,  true)  => None()
  } in
  match (t, result) {
    (Instruction, None()) => MemException(E_Fetch_Access_Fault),
    (Data, None())        => MemException(E_Load_Access_Fault),
    (_, Some(v))          => { print("mem[" ^ t ^ "," ^ BitStr(addr) ^ "] -> " ^ BitStr(v));
                               MemValue(v) }
  }

function checked_mem_read(t : ReadType, addr : xlenbits, width : atom('n), aq : bool, rl : bool, res : bool) -> forall 'n, 'n > 0. MemoryOpResult(bits(8 * 'n)) =
  /* treat MMIO regions as not executable for now. TODO: this should actually come from PMP/PMA. */
  /* TODO: aq/rl/res to MMIO */
  if   t == Data & within_mmio_readable(addr, width) & aq == false & rl == false & res == false
  then mmio_read(addr, width)
  else if within_phys_mem(addr, width)
  then phys_mem_read(t, addr, width, aq, rl, res)
  else MemException(E_Load_Access_Fault)

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

/* NOTE: The rreg effect is due to MMIO. */
val mem_read : forall 'n, 'n > 0. (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg, escape}

function mem_read (addr, width, aq, rl, res) = {
  if (aq | res) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_Load_Addr_Align)
  else match (aq, rl, res) {
    (false, true,  false) => throw(Error_not_implemented("load.rl")),
    (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
    _ => checked_mem_read(Data, addr, width, aq, rl, res)
  }
}

val mem_write_ea : forall 'n, 'n > 0. (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(unit) effect {eamem, escape}

function mem_write_ea (addr, width, aq, rl, con) = {
  if (rl | con) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_SAMO_Addr_Align)
  else match (aq, rl, con) {
    (false, false, false) => { __write_ea(Write_plain, addr, width); MemValue(()) },
    (false, true,  false) => { __write_ea(Write_RISCV_release, addr, width); MemValue(()) },
    (false, false, true)  => { __write_ea(Write_RISCV_conditional, addr, width); MemValue(()) },
    (false, true , true)  => { __write_ea(Write_RISCV_conditional_release, addr, width); MemValue(()) },
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => { __write_ea(Write_RISCV_strong_release, addr, width); MemValue(()) },
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true , true)  => { __write_ea(Write_RISCV_conditional_strong_release, addr, width); MemValue(()) }
  }
}

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_write(addr : xlenbits, width : atom('n), data: bits(8 * 'n), aq : bool, rl : bool, con : bool) -> forall 'n, 'n > 0. MemoryOpResult(bool) = {
  print("mem[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data));
  MemValue(__write_memv(data))
}

// dispatches to MMIO regions or physical memory regions depending on physical memory map
function checked_mem_write(addr : xlenbits, width : atom('n), data: bits(8 * 'n), aq : bool, rl : bool, con : bool) -> forall 'n, 'n > 0. MemoryOpResult(bool) =
  /* TODO: aq/rl/con to MMIO */
  if   within_mmio_writable(addr, width) & aq == false & rl == false & con == false
  then mmio_write(addr, width, data)
  else if within_phys_mem(addr, width)
  then phys_mem_write(addr, width, data, aq, rl, con)
  else MemException(E_SAMO_Access_Fault)

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

/* NOTE: The wreg effect is due to MMIO, the rreg is due to checking mtime. */
val mem_write_value : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n), bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, rreg, wreg, escape}

function mem_write_value (addr, width, value, aq, rl, con) = {
  if (rl | con) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_SAMO_Addr_Align)
  else match (aq, rl, con) {
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    _ => checked_mem_write(addr, width, value, aq, rl, con)
  }
}

val mem_barrier : barrier_kind -> unit effect {barr}
function mem_barrier bk = __barrier(bk)
