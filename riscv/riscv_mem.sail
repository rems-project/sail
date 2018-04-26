/* memory */

union MemoryOpResult ('a : Type) = {
  MemValue : 'a,
  MemException: ExceptionType
}

function is_aligned_addr (addr : xlenbits, width : atom('n)) -> forall 'n. bool =
  unsigned(addr) % width != 0

function checked_mem_read(t : ReadType, addr : xlenbits, width : atom('n)) -> forall 'n. MemoryOpResult(bits(8 * 'n)) =
  match (t, __RISCV_read(addr, width)) {
    (Instruction, None()) => MemException(E_Fetch_Access_Fault),
    (Data, None())        => MemException(E_Load_Access_Fault),
    (_, Some(v))          => MemValue(v)
  }

val MEMr                         : forall 'n. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem}
val MEMr_acquire                 : forall 'n. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem}
val MEMr_strong_acquire          : forall 'n. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem}
val MEMr_reserved                : forall 'n. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem}
val MEMr_reserved_acquire        : forall 'n. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem}
val MEMr_reserved_strong_acquire : forall 'n. (xlenbits, atom('n)) -> MemoryOpResult(bits(8 * 'n)) effect {rmem}

function MEMr                         (addr, width) = checked_mem_read(Data, addr, width)
function MEMr_acquire                 (addr, width) = checked_mem_read(Data, addr, width)
function MEMr_strong_acquire          (addr, width) = checked_mem_read(Data, addr, width)
function MEMr_reserved                (addr, width) = checked_mem_read(Data, addr, width)
function MEMr_reserved_acquire        (addr, width) = checked_mem_read(Data, addr, width)
function MEMr_reserved_strong_acquire (addr, width) = checked_mem_read(Data, addr, width)

val mem_read : forall 'n. (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, escape}

function mem_read (addr, width, aq, rl, res) = {
  if (aq | res) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_Load_Addr_Align)
  else match (aq, rl, res) {
    (false, false, false) => MEMr(addr, width),
    (true,  false, false) => MEMr_acquire(addr, width),
    (false, false, true)  => MEMr_reserved(addr, width),
    (true,  false, true)  => MEMr_reserved_acquire(addr, width),
    (false, true,  false) => throw(Error_not_implemented("load.rl")),
    (true,  true,  false) => MEMr_strong_acquire(addr, width),
    (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
    (true,  true,  true)  => MEMr_reserved_strong_acquire(addr, width)
  }
}

val MEMea = {ocaml: "memea", lem: "MEMea"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_release = {ocaml: "memea", lem: "MEMea_release"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_strong_release = {ocaml: "memea", lem: "MEMea_strong_release"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_conditional = {ocaml: "memea", lem: "MEMea_conditional"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_conditional_release = {ocaml: "memea", lem: "MEMea_conditional_release"} : forall 'n.
  (xlenbits, atom('n)) -> unit effect {eamem}
val MEMea_conditional_strong_release = {ocaml: "memea", lem: "MEMea_conditional_strong_release"} : forall 'n.
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

function checked_mem_write(addr : xlenbits, width : atom('n), data: bits(8 * 'n)) -> forall 'n. MemoryOpResult(unit) =
  if (__RISCV_write(addr, width, data))
  then MemValue(())
  else MemException(E_SAMO_Access_Fault)

val MEMval                            : forall 'n. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wmv}
val MEMval_release                    : forall 'n. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wmv}
val MEMval_strong_release             : forall 'n. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wmv}
val MEMval_conditional                : forall 'n. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wmv}
val MEMval_conditional_release        : forall 'n. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wmv}
val MEMval_conditional_strong_release : forall 'n. (xlenbits, atom('n), bits(8 * 'n)) -> MemoryOpResult(unit) effect {wmv}

function MEMval                            (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_release                    (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_strong_release             (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_conditional                (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_conditional_release        (addr, width, data) = checked_mem_write(addr, width, data)
function MEMval_conditional_strong_release (addr, width, data) = checked_mem_write(addr, width, data)


val mem_write_value : forall 'n. (xlenbits, atom('n), bits(8 * 'n), bool, bool, bool) -> MemoryOpResult(unit) effect {wmv, escape}

function mem_write_value (addr, width, value, aq, rl, con) = {
  if (rl | con) & (~ (is_aligned_addr(addr, width)))
  then MemException(E_SAMO_Addr_Align)
  else match (aq, rl, con) {
    (false, false, false) => MEMval(addr, width, value),
    (false, true,  false) => MEMval_release(addr, width, value),
    (false, false, true)  => MEMval_conditional(addr, width, value),
    (false, true,  true)  => MEMval_conditional_release(addr, width, value),
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => MEMval_strong_release(addr, width, value),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true,  true)  => MEMval_conditional_strong_release(addr, width, value)
  }
}

val "speculate_conditional_success" : unit -> bool effect {exmem}

val MEM_fence_rw_rw = {ocaml: "skip", lem: "MEM_fence_rw_rw"} : unit -> unit effect {barr}
val MEM_fence_r_rw  = {ocaml: "skip", lem: "MEM_fence_r_rw"}  : unit -> unit effect {barr}
val MEM_fence_r_r   = {ocaml: "skip", lem: "MEM_fence_r_r"}   : unit -> unit effect {barr}
val MEM_fence_rw_w  = {ocaml: "skip", lem: "MEM_fence_rw_w"}  : unit -> unit effect {barr}
val MEM_fence_w_w   = {ocaml: "skip", lem: "MEM_fence_w_w"}   : unit -> unit effect {barr}
val MEM_fence_i     = {ocaml: "skip", lem: "MEM_fence_i"}     : unit -> unit effect {barr}
