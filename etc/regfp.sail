(* iR : input registers,
 * oR : output registers,
 * aR : registers feeding into the memory address *)

(* branch instructions currently are not writing to NIA *)

typedef regfp = const union {
   (string) RFull;
   (string,nat,nat) RSlice;
   (string,nat) RSliceBit;
   (string,string) RField;
}

typedef regfps = list <regfp>

typedef niafp = const union {
  NIAFP_successor;
  (bit[64]) NIAFP_concrete_address;
  NIAFP_indirect_address;
}

typedef niafps = list <niafp>

(* only for MIPS *)
typedef diafp = const union {
  DIAFP_none;
  (bit[64]) DIAFP_concrete;
  (regfp) DIAFP_reg;
}

typedef read_kind = enumerate {
  Read_plain;
  Read_reserve;
  Read_acquire;
  Read_exclusive;
  Read_exclusive_acquire;
  Read_stream;
  Read_RISCV_acquire_RCpc;
  Read_RISCV_acquire_RCsc;
  Read_RISCV_acquire_release;
  Read_RISCV_reserved;
  Read_RISCV_reserved_acquire_RCpc;
  Read_RISCV_reserved_acquire_RCsc;
  Read_RISCV_reserved_acquire_release;
  Read_X86_locked;
}

typedef write_kind = enumerate {
  Write_plain;
  Write_conditional;
  Write_release;
  Write_exclusive;
  Write_exclusive_release;
  Write_RISCV_release_RCpc;
  Write_RISCV_release_RCsc;
  Write_RISCV_acquire_release;
  Write_RISCV_conditional;
  Write_RISCV_conditional_release_RCpc;
  Write_RISCV_conditional_release_RCsc;
  Write_RISCV_conditional_acquire_release;
  Write_X86_locked;
}

typedef barrier_kind = enumerate {
  Barrier_Sync;
  Barrier_LwSync;
  Barrier_Eieio;
  Barrier_Isync;
  Barrier_DMB;
  Barrier_DMB_ST;
  Barrier_DMB_LD;
  Barrier_DSB;
  Barrier_DSB_ST;
  Barrier_DSB_LD;
  Barrier_ISB;
  Barrier_MIPS_SYNC;
  Barrier_RISCV_rw_rw;
  Barrier_RISCV_r_rw;
  Barrier_RISCV_w_rw;
  Barrier_RISCV_rw_r;
  Barrier_RISCV_r_r;
  Barrier_RISCV_w_r;
  Barrier_RISCV_rw_w;
  Barrier_RISCV_r_w;
  Barrier_RISCV_w_w;
  Barrier_RISCV_tso;
  Barrier_RISCV_i;
  Barrier_x86_MFENCE;
}

typedef trans_kind = enumerate {
  Transaction_start; Transaction_commit; Transaction_abort;
}

(* cache maintenance instructions *)
typedef cache_op_kind = enumerate {
  (* AArch64 DC *)
  Cache_op_D_IVAC; Cache_op_D_ISW;  Cache_op_D_CSW;  Cache_op_D_CISW;
  Cache_op_D_ZVA;  Cache_op_D_CVAC; Cache_op_D_CVAU; Cache_op_D_CIVAC;
  (* AArch64 IC *)
  Cache_op_I_IALLUIS; Cache_op_I_IALLU; Cache_op_I_IVAU;
}

typedef instruction_kind = const union {
  (barrier_kind) IK_barrier;
  (read_kind) IK_mem_read;
  (write_kind) IK_mem_write;
  (read_kind, write_kind) IK_mem_rmw;
  IK_branch;
  (trans_kind) IK_trans;
  IK_simple;
  (cache_op_kind) IK_cache_op
}
