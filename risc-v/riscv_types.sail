default Order dec

function forall 'a. 'a effect { escape } not_implemented((string) message) =
  exit message

typedef regval = bit[64]
typedef regno = bit[5]

(* register (regval) x0 is hard-wired zero *)
register (regval) x1
register (regval) x2
register (regval) x3
register (regval) x4
register (regval) x5
register (regval) x6
register (regval) x7
register (regval) x8
register (regval) x9
register (regval) x10
register (regval) x11
register (regval) x12
register (regval) x13
register (regval) x14
register (regval) x15
register (regval) x16
register (regval) x17
register (regval) x18
register (regval) x19
register (regval) x20
register (regval) x21
register (regval) x22
register (regval) x23
register (regval) x24
register (regval) x25
register (regval) x26
register (regval) x27
register (regval) x28
register (regval) x29
register (regval) x30
register (regval) x31

register (bit[64]) PC
register (bit[64]) nextPC

let (vector <1, 31, inc, (register<(regval)>)>) GPRs =
  [ (* x0, *) x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
    x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27,
    x28, x29, x30, x31
  ]

function (regval) rGPR ((regno) r) =
    if (r == 0) then
        0
    else
        GPRs[r]

function unit wGPR((regno) r, (regval) v) =
    if (r != 0) then
        GPRs[r] := v

function unit effect { escape } check_alignment( (bit[64]) addr, (nat) width) =
  if (unsigned(addr) mod width != 0) then
    exit "misaligned memory access"

val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_acquire
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_strong_acquire
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserved
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserved_acquire
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserved_strong_acquire

function forall Nat 'n. (bit[8 * 'n]) effect { rmem, escape } mem_read( (bit[64]) addr, ([|'n|]) width, (bool) aq, (bool) rl, (bool) res) =
{
  if (aq | res) then
    check_alignment(addr, width);

  switch (aq, rl, res) {
    case (false, false, false) -> MEMr(addr, width)
    case (true,  false, false) -> MEMr_acquire(addr, width)
    case (false, false, true)  -> MEMr_reserved(addr, width)
    case (true,  false, true)  -> MEMr_reserved_acquire(addr, width)
    case (false, true,  false) -> not_implemented("load.rl is not implemented")
    case (true,  true,  false) -> MEMr_strong_acquire(addr, width)
    case (false, true,  true)  -> not_implemented("lr.rl is not implemented")
    case (true,  true,  true)  -> MEMr_reserved_strong_acquire(addr, width)
  }
}

val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_release
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_strong_release
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_conditional
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_conditional_release
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_conditional_strong_release

function forall Nat 'n. unit effect { eamem, escape } mem_write_ea( (bit[64]) addr , ([|'n|]) width, (bool) aq, (bool) rl, (bool) con) =
{
  if (rl | con) then
    check_alignment(addr, width);

  switch (aq, rl, con) {
    case (false, false, false) -> MEMea(addr, width)
    case (false, true,  false) -> MEMea_release(addr, width)
    case (false, false, true)  -> MEMea_conditional(addr, width)
    case (false, true , true)  -> MEMea_conditional_release(addr, width)
    case (true,  false, false) -> not_implemented("store.aq is not implemented")
    case (true,  true,  false) -> MEMea_strong_release(addr, width)
    case (true,  false, true)  -> not_implemented("sc.aq is not implemented")
    case (true,  true , true)  -> MEMea_conditional_strong_release(addr, width)
  }
}

val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval_release
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval_strong_release
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval_conditional
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval_conditional_release
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval_conditional_strong_release

function forall Nat 'n. unit effect { wmv, escape } mem_write_value( (bit[64]) addr , ([|'n|]) width , (bit[8*'n]) value, (bool) aq, (bool) rl, (bool) con) =
{
  if (rl | con) then
    check_alignment(addr, width);

  switch (aq, rl, con) {
    case (false, false, false) -> MEMval(addr, width, value)
    case (false, true,  false) -> MEMval_release(addr, width, value)
    case (false, false, true)  -> MEMval_conditional(addr, width, value)
    case (false, true,  true)  -> MEMval_conditional_release(addr, width, value)
    case (true,  false, false) -> not_implemented("store.aq is not implemented")
    case (true,  true,  false) -> MEMval_strong_release(addr, width, value)
    case (true,  false, true)  -> not_implemented("sc.aq is not implemented")
    case (true,  true,  true)  -> MEMval_conditional_strong_release(addr, width, value)
  }
}

val extern unit -> bool effect {exmem} speculate_conditional_success

val extern unit -> unit effect { barr } MEM_fence_rw_rw
val extern unit -> unit effect { barr } MEM_fence_r_rw
val extern unit -> unit effect { barr } MEM_fence_r_r
val extern unit -> unit effect { barr } MEM_fence_rw_w
val extern unit -> unit effect { barr } MEM_fence_w_w
val extern unit -> unit effect { barr } MEM_fence_i

typedef uop = enumerate {LUI; AUIPC} (* upper immediate ops *)
typedef bop = enumerate {BEQ; BNE; BLT; BGE; BLTU; BGEU} (* branch ops *)
typedef iop = enumerate {ADDI; SLTI; SLTIU; XORI; ORI; ANDI} (* immediate ops *)
typedef sop = enumerate {SLLI; SRLI; SRAI} (* shift ops *)
typedef rop = enumerate {ADD; SUB; SLL; SLT; SLTU; XOR; SRL; SRA; OR; AND} (* reg-reg ops *)
typedef ropw = enumerate {ADDW; SUBW; SLLW; SRLW; SRAW} (* reg-reg 32-bit ops *)
typedef amoop = enumerate {AMOSWAP; AMOADD; AMOXOR; AMOAND; AMOOR;
    AMOMIN; AMOMAX; AMOMINU; AMOMAXU} (* AMO ops *)

typedef word_width = enumerate {BYTE; HALF; WORD; DOUBLE}

(********************************************************************)

(* Ideally these would be sail builtin *)
function (bit[64]) shift_right_arith64 ((bit[64]) v, (bit[6]) shift) =
    let (bit[128]) v128 = EXTS(v) in
    (v128 >> shift)[63..0]

function (bit[32]) shift_right_arith32 ((bit[32]) v, (bit[5]) shift) =
    let (bit[64]) v64 = EXTS(v) in
    (v64 >> shift)[31..0]
