$ifndef _REGFP
$define _REGFP

/* iR : input registers,
 * oR : output registers,
 * aR : registers feeding into the memory address */
 
/* branch instructions currently are not writing to NIA */

union regfp = {
   RFull : string,
   RSlice : (string,nat,nat),
   RSliceBit : (string,nat),
   RField : (string,string)
}

type regfps = list(regfp)

union niafp = {
  NIAFP_successor : unit,
  NIAFP_concrete_address : bits(64),
  NIAFP_indirect_address : unit
}

type niafps = list(niafp)

/* only for MIPS */
union diafp = {
  DIAFP_none : unit,
  DIAFP_concrete : bits(64),
  DIAFP_reg : regfp
}

enum read_kind = {
  Read_plain,
  Read_reserve,
  Read_acquire,
  Read_exclusive,
  Read_exclusive_acquire,
  Read_stream,
  Read_RISCV_acquire,
  Read_RISCV_strong_acquire,
  Read_RISCV_reserved,
  Read_RISCV_reserved_acquire,
  Read_RISCV_reserved_strong_acquire,
  Read_X86_locked
}

enum write_kind = {
  Write_plain,
  Write_conditional,
  Write_release,
  Write_exclusive,
  Write_exclusive_release,
  Write_RISCV_release,
  Write_RISCV_strong_release,
  Write_RISCV_conditional,
  Write_RISCV_conditional_release,
  Write_RISCV_conditional_strong_release,
  Write_X86_locked
}

enum barrier_kind = {
  Barrier_Sync,
  Barrier_LwSync,
  Barrier_Eieio,
  Barrier_Isync,
  Barrier_DMB,
  Barrier_DMB_ST,
  Barrier_DMB_LD,
  Barrier_DSB,
  Barrier_DSB_ST,
  Barrier_DSB_LD,
  Barrier_ISB,
  Barrier_MIPS_SYNC,
  Barrier_RISCV_rw_rw,
  Barrier_RISCV_r_rw,
  Barrier_RISCV_r_r,
  Barrier_RISCV_rw_w,
  Barrier_RISCV_w_w,
  Barrier_RISCV_w_rw,
  Barrier_RISCV_rw_r,
  Barrier_RISCV_r_w,
  Barrier_RISCV_w_r,
  Barrier_RISCV_i,
  Barrier_x86_MFENCE
}

enum trans_kind = {
  Transaction_start,
  Transaction_commit,
  Transaction_abort
}

union instruction_kind = {
  IK_barrier : barrier_kind,
  IK_mem_read : read_kind,
  IK_mem_write : write_kind,
  IK_mem_rmw : (read_kind, write_kind),
  IK_branch : unit,
  IK_trans : trans_kind,
  IK_simple : unit
}

val __read_mem = { ocaml: "Platform.read_mem", _: "read_mem" } : forall 'n, 'n > 0. (read_kind, bits(64), int('n)) -> bits(8 * 'n) effect {rmem}
val __write_ea = { ocaml: "Platform.write_ea", _: "write_ea" } : forall 'n, 'n > 0. (write_kind, bits(64), int('n)) -> unit effect {eamem}
val __write_memv = { ocaml: "Platform.write_memv", _: "write_memv" } : forall 'n, 'n > 0. bits('n) -> bool effect {wmv}
val __excl_res = { ocaml: "Platform.excl_res", _: "excl_res" }: unit -> bool effect {exmem}
val __barrier = { ocaml: "Platform.barrier", _: "barrier" } : barrier_kind -> unit effect {barr}

val __write_mem : forall 'n, 'n > 0. (write_kind, bits(64), int('n), bits(8 * 'n)) -> bool effect {eamem,wmv}
function __write_mem (wk, addr, len, value) = {
  __write_ea(wk, addr, len);
  __write_memv(value)
}

$endif
