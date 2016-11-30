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
  NIAFP_LR;
  NIAFP_CTR;
  (regfp) NIAFP_register;
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
  Read_tag;
  Read_reserve;
  Read_acquire;
  Read_exclusive;
  Read_exclusive_acquire;
  Read_stream
}

typedef write_kind = enumerate {
  Write_plain;
  Write_tag;
  Write_conditional;
  Write_release;
  Write_exclusive;
  Write_exclusive_release;
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
}

typedef instruction_kind = const union {
  (barrier_kind) IK_barrier;
  (read_kind) IK_mem_read;
  (write_kind) IK_mem_write;
  IK_cond_branch;
  IK_simple
}
