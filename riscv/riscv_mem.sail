/* Physical memory model.
 *
 * This assumes that the platform memory map has been defined, so that accesses
 * to MMIO regions can be dispatched.
 */

function is_aligned_addr (addr : xlenbits, width : atom('n)) -> forall 'n. bool =
  unsigned(addr) % width == 0

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_read(t : ReadType, addr : xlenbits, width : atom('n), aq : bool, rl: bool, res : bool) -> forall 'n, 'n >= 0. MemoryOpResult(bits(8 * 'n)) =
  match (t, __RISCV_read(addr, width, aq, rl, res)) {
    (Instruction, None()) => MemException(E_Fetch_Access_Fault),
    (Data, None())        => MemException(E_Load_Access_Fault),
    (_, Some(v))          => { print("mem[" ^ t ^ "," ^ BitStr(addr) ^ "] -> " ^ BitStr(v));
                               MemValue(v) }
  }

function checked_mem_read(t : ReadType, addr : xlenbits, width : atom('n), aq : bool, rl : bool, res: bool) -> forall 'n, 'n > 0. MemoryOpResult(bits(8 * 'n)) =
  /* treat MMIO regions as not executable for now. TODO: this should actually come from PMP/PMA. */
  if   t == Data & within_mmio_readable(addr, width)
  then mmio_read(addr, width)
  else if within_phys_mem(addr, width)
  then phys_mem_read(t, addr, width, aq, rl, res)
  else MemException(E_Load_Access_Fault)

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

val MEMr                         : forall 'n, 'n > 0. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg}
val MEMr_acquire                 : forall 'n, 'n > 0. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg}
val MEMr_strong_acquire          : forall 'n, 'n > 0. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg}
val MEMr_reserved                : forall 'n, 'n > 0. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg}
val MEMr_reserved_acquire        : forall 'n, 'n > 0. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg}
val MEMr_reserved_strong_acquire : forall 'n, 'n > 0. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg}

function MEMr                         (addr, width) = checked_mem_read(Data, addr, width, false, false, false)
function MEMr_acquire                 (addr, width) = checked_mem_read(Data, addr, width, true, false, false)
function MEMr_strong_acquire          (addr, width) = checked_mem_read(Data, addr, width, true, true, false)
function MEMr_reserved                (addr, width) = checked_mem_read(Data, addr, width, false, false, true)
function MEMr_reserved_acquire        (addr, width) = checked_mem_read(Data, addr, width, true, false, true)
function MEMr_reserved_strong_acquire (addr, width) = checked_mem_read(Data, addr, width, true, true, true)

$ifdef RVFI_DII
val rvfi_read : forall 'n, 'n > 0. (xlenbits, atom('n), MemoryOpResult(bits(8 * 'n))) -> unit effect {wreg}
function rvfi_read (addr, width, result) = {
  rvfi_exec->rvfi_mem_addr() = addr;
  match result {
  MemValue(v) =>
    if width <= 8
    then {
      rvfi_exec->rvfi_mem_wdata() = zero_extend(v,64);
      rvfi_exec->rvfi_mem_wmask() = to_bits(8,width)
    } else (),
  MemException(_) => ()
  };
}
$else
val rvfi_read : forall 'n, 'n > 0. (xlenbits, atom('n), MemoryOpResult(bits(8 * 'n))) -> unit
function rvfi_read (addr, width, value) = ()
$endif

/* NOTE: The rreg effect is due to MMIO. */
$ifdef RVFI_DII
val mem_read : forall 'n, 'n > 0. (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(bits(8 * 'n)) effect {wreg, rmem, rreg, escape}
$else
val mem_read : forall 'n, 'n > 0. (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rreg, escape}
$endif

function mem_read (addr, width, aq, rl, res) = {
 let result : MemoryOpResult(bits(8 * 'n)) =
  if (aq | res) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_Load_Addr_Align)
  else match (aq, rl, res) {
    (false, false, false) => checked_mem_read(Data, addr, width, false, false, false),
    (true,  false, false) => MEMr_acquire(addr, width),
    (false, false, true)  => MEMr_reserved(addr, width),
    (true,  false, true)  => MEMr_reserved_acquire(addr, width),
    (false, true,  false) => throw(Error_not_implemented("load.rl")),
    (true,  true,  false) => MEMr_strong_acquire(addr, width),
    (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
    (true,  true,  true)  => MEMr_reserved_strong_acquire(addr, width)
  };
 rvfi_read(addr, width, result);
 result
}

val MEMea = {lem: "MEMea", coq: "MEMea", _: "memea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_release = {lem: "MEMea_release", coq: "MEMea_release", _: "memea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_strong_release = {lem: "MEMea_strong_release", coq: "MEMea_strong_release", _: "memea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_conditional = {lem: "MEMea_conditional", coq: "MEMea_conditional", _: "memea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_conditional_release = {lem: "MEMea_conditional_release", coq: "MEMea_conditional_release", _: "memea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_conditional_strong_release = {lem: "MEMea_conditional_strong_release", coq: "MEMea_conditional_strong_release", _: "memea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}

val mem_write_ea : forall 'n. (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(unit) effect {eamem, escape}

function mem_write_ea (addr, width, aq, rl, con) = {
  if (rl | con) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_SAMO_Addr_Align)
  else match (aq, rl, con) {
    (false, false, false) => MemValue(MEMea(addr, width)),
    (false, true,  false) => MemValue(MEMea_release(addr, width)),
    (false, false, true)  => MemValue(MEMea_conditional(addr, width)),
    (false, true , true)  => MemValue(MEMea_conditional_release(addr, width)),
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => MemValue(MEMea_strong_release(addr, width)),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true , true)  => MemValue(MEMea_conditional_strong_release(addr, width))
  }
}

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_write(addr : xlenbits, width : atom('n), data: bits(8 * 'n)) -> forall 'n. MemoryOpResult(bool) = {
  print("mem[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data));
  MemValue(__RISCV_write(addr, width, data))
}

// dispatches to MMIO regions or physical memory regions depending on physical memory map
function checked_mem_write(addr : xlenbits, width : atom('n), data: bits(8 * 'n)) -> forall 'n, 'n > 0. MemoryOpResult(bool) =
  if   within_mmio_writable(addr, width)
  then mmio_write(addr, width, data)
  else if within_phys_mem(addr, width)
  then phys_mem_write(addr, width, data)
  else MemException(E_SAMO_Access_Fault)

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

val MEMval                            : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wmv, rreg, wreg}
val MEMval_release                    : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wmv, rreg, wreg}
val MEMval_strong_release             : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wmv, rreg, wreg}
val MEMval_conditional                : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wmv, rreg, wreg}
val MEMval_conditional_release        : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wmv, rreg, wreg}
val MEMval_conditional_strong_release : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(bool) effect {wmv, rreg, wreg}

function MEMval                            (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_release                    (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_strong_release             (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_conditional                (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_conditional_release        (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_conditional_strong_release (addr, width, data) = checked_mem_write(addr, width, data)


$ifdef RVFI_DII
val rvfi_write : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> unit effect {wreg}
function rvfi_write (addr, width, value) = {
  rvfi_exec->rvfi_mem_addr() = addr;
  if width <= 8 then {
    rvfi_exec->rvfi_mem_wdata() = zero_extend(value,64);
    rvfi_exec->rvfi_mem_wmask() = to_bits(8,width);
  }
}
$else
val rvfi_write : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n)) -> unit
function rvfi_write (addr, width, value) = ()
$endif

/* NOTE: The wreg effect is due to MMIO, the rreg is due to checking mtime. */
val mem_write_value : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n), bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, rreg, wreg, escape}

function mem_write_value (addr, width, value, aq, rl, con) = {
  rvfi_write(addr, width, value);
  if (rl | con) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_SAMO_Addr_Align)
  else match (aq, rl, con) {
    (false, false, false) => checked_mem_write(addr, width, value),
    (false, true,  false) => MEMval_release(addr, width, value),
    (false, false, true)  => MEMval_conditional(addr, width, value),
    (false, true,  true)  => MEMval_conditional_release(addr, width, value),
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => MEMval_strong_release(addr, width, value),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true,  true)  => MEMval_conditional_strong_release(addr, width, value)
  }
}

val MEM_fence_rw_rw = {lem: "MEM_fence_rw_rw", coq: "MEM_fence_rw_rw", _: "skip"} : unit -> unit effect {barr}
val MEM_fence_r_rw  = {lem: "MEM_fence_r_rw", coq: "MEM_fence_r_rw", _: "skip"}  : unit -> unit effect {barr}
val MEM_fence_r_r   = {lem: "MEM_fence_r_r", coq: "MEM_fence_r_r", _: "skip"}   : unit -> unit effect {barr}
val MEM_fence_rw_w  = {lem: "MEM_fence_rw_w", coq: "MEM_fence_rw_w", _: "skip"}  : unit -> unit effect {barr}
val MEM_fence_w_w   = {lem: "MEM_fence_w_w", coq: "MEM_fence_w_w", _: "skip"}   : unit -> unit effect {barr}
val MEM_fence_w_rw  = {lem: "MEM_fence_w_rw", coq: "MEM_fence_w_rw", _: "skip"}  : unit -> unit effect {barr}
val MEM_fence_rw_r  = {lem: "MEM_fence_rw_r", coq: "MEM_fence_rw_r", _: "skip"}  : unit -> unit effect {barr}
val MEM_fence_r_w   = {lem: "MEM_fence_r_w", coq: "MEM_fence_r_w", _: "skip"}   : unit -> unit effect {barr}
val MEM_fence_w_r   = {lem: "MEM_fence_w_r", coq: "MEM_fence_w_r", _: "skip"}   : unit -> unit effect {barr}
val MEM_fence_i     = {lem: "MEM_fence_i", coq: "MEM_fence_i", _: "skip"}     : unit -> unit effect {barr}
