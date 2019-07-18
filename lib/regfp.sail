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

enum a64_barrier_domain = {
  A64_FullShare,
  A64_InnerShare,
  A64_OuterShare,
  A64_NonShare
}

enum a64_barrier_type = {
  A64_barrier_all,
  A64_barrier_LD,
  A64_barrier_ST
}

$ifdef AARCH64_SMALL
union barrier_kind = {
  Barrier_Sync : unit,
  Barrier_LwSync : unit,
  Barrier_Eieio : unit,
  Barrier_Isync : unit,
  Barrier_DMB : (a64_barrier_domain, a64_barrier_type),
  Barrier_DSB : (a64_barrier_domain, a64_barrier_type),
  Barrier_ISB : unit,
  Barrier_MIPS_SYNC : unit,
  Barrier_RISCV_rw_rw : unit,
  Barrier_RISCV_r_rw : unit,
  Barrier_RISCV_r_r : unit,
  Barrier_RISCV_rw_w : unit,
  Barrier_RISCV_w_w : unit,
  Barrier_RISCV_w_rw : unit,
  Barrier_RISCV_rw_r : unit,
  Barrier_RISCV_r_w : unit,
  Barrier_RISCV_w_r : unit,
  Barrier_RISCV_tso : unit,
  Barrier_RISCV_i : unit,
  Barrier_x86_MFENCE : unit
}
$else
enum barrier_kind = {
  Barrier_Sync,
  Barrier_LwSync,
  Barrier_Eieio,
  Barrier_Isync,
  Barrier_DMB,
  Barrier_DSB,
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
  Barrier_RISCV_tso,
  Barrier_RISCV_i,
  Barrier_x86_MFENCE
}
$endif

enum trans_kind = {
  Transaction_start,
  Transaction_commit,
  Transaction_abort
}

/* cache maintenance instructions */
enum cache_op_kind = {
  /* AArch64 DC */
  Cache_op_D_IVAC, Cache_op_D_ISW,  Cache_op_D_CSW,  Cache_op_D_CISW,
  Cache_op_D_ZVA,  Cache_op_D_CVAC, Cache_op_D_CVAU, Cache_op_D_CIVAC,
  /* AArch64 IC */
  Cache_op_I_IALLUIS, Cache_op_I_IALLU, Cache_op_I_IVAU
}


union instruction_kind = {
  IK_barrier : barrier_kind,
  IK_mem_read : read_kind,
  IK_mem_write : write_kind,
  IK_mem_rmw : (read_kind, write_kind),
  IK_branch : unit,
  IK_trans : trans_kind,
  IK_simple : unit,
  IK_cache_op : cache_op_kind
}

val __read_mem
  = { ocaml: "Platform.read_mem", c: "platform_read_mem", _: "read_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n) effect {rmem}
val __write_mem_ea
  = { ocaml: "Platform.write_mem_ea", c: "platform_write_mem_ea", _: "write_mem_ea" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n)) -> unit effect {eamem}
val __write_mem
  = { ocaml: "Platform.write_mem", c: "platform_write_mem", _: "write_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmv}
val __excl_res
  = { ocaml: "Platform.excl_res", c: "platform_excl_res", _: "excl_result" }
  : unit -> bool effect {exmem}
val __barrier
  = { ocaml: "Platform.barrier", c: "platform_barrier", _: "barrier" }
  : barrier_kind -> unit effect {barr}


/*
val __write : forall 'n, 'n > 0. (write_kind, bits(64), int('n), bits(8 * 'n)) -> bool effect {eamem,wmv}
function __write (wk, addr, len, value) = {
  __write_mem_ea(wk, addr, len);
  __write_mem(wk, addr, len, value)
}
*/

$endif
