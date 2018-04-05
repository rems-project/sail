function clause decode (0b10011011 @ _ : bits(1) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op54 : bits(2) = op_code[30 .. 29];
  U : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_mul_widening_64128hi_decode(sf, op54, U, Rm, o0, Ra, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b1010001 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_general_postidx_aarch64_memory_pair_general_postidx__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b1010011 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_general_preidx_aarch64_memory_pair_general_postidx__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b1010010 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_general_offset_aarch64_memory_pair_general_postidx__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  option_name : bits(3) = op_code[15 .. 13];
  S : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_simdfp_register_aarch64_memory_single_simdfp_register__decode(size, V, opc, Rm, option_name, S, Rn, Rt)
}

function clause decode (0b00011111 @ _ : bits(24) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  o1 : bits(1) = [op_code[21]];
  Rm : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_mul_addsub_decode(M, S, typ, o1, Rm, o0, Ra, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0 @ _ : bits(3) @ 0b00 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  A : bits(1) = [op_code[23]];
  R : bits(1) = [op_code[22]];
  Rs : bits(5) = op_code[20 .. 16];
  o3 : bits(1) = [op_code[15]];
  opc : bits(3) = op_code[14 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_atomicops_ld_decode(size, V, A, R, Rs, o3, opc, Rn, Rt)
}

function clause decode (0b110110101100000101000 @ _ : bits(11) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  D : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_strip_dp_1src_decode(sf, S, opcode2, D, Rn, Rd)
}

function clause decode (0b11010101000000110010000011111111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  integer_pac_strip_hint_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b010 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_pacda_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b01011111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  system_monitors_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_offset_normal_aarch64_memory_single_general_immediate_signed_offset_normal__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b1010000 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_general_noalloc_aarch64_memory_pair_general_noalloc__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(6) @ 0b00010 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[15]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_mul_product_decode(M, S, typ, Rm, op, Rn, Rd)
}

function clause decode (0b10011010110 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode2 : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_pacga_dp_2src_decode(sf, op, S, Rm, opcode2, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b0010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  o2 : bits(1) = [op_code[23]];
  L : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[21]];
  Rs : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_atomicops_cas_single_decode(size, o2, L, o1, Rs, o0, Rt2, Rn, Rt)
}

function clause decode (0b1101010100000 @ _ : bits(3) @ 0b0100 @ _ : bits(7) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  system_register_cpsr_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (0b01010100 @ _ : bits(19) @ 0b0 @ _ : bits(4) as op_code) = {
  o1 : bits(1) = [op_code[24]];
  imm19 : bits(19) = op_code[23 .. 5];
  o0 : bits(1) = [op_code[4]];
  cond : bits(4) = op_code[3 .. 0];
  branch_conditional_cond_decode(o1, imm19, o0, cond)
}

function clause decode (0b11010100000 @ _ : bits(16) @ 0b00010 as op_code) = {
  opc : bits(3) = op_code[23 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  op2 : bits(3) = op_code[4 .. 2];
  LL : bits(2) = op_code[1 .. 0];
  system_exceptions_runtime_hvc_decode(opc, imm16, op2, LL)
}

function clause decode (0b1 @ _ : bits(1) @ 0b0010000 @ _ : bits(1) @ 0b1 @ _ : bits(21) as op_code) = {
  sz : bits(1) = [op_code[30]];
  o2 : bits(1) = [op_code[23]];
  L : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[21]];
  Rs : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_exclusive_pair_decode(sz, o2, L, o1, Rs, o0, Rt2, Rn, Rt)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b111 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_autdb_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b101101011000000000000 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_rbit_decode(sf, S, opcode2, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111001 @ _ : bits(24) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_unsigned__decode(size, V, opc, imm12, Rn, Rt)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_autia_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  integer_pac_autia_hint_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (0b11010100000 @ _ : bits(16) @ 0b00001 as op_code) = {
  opc : bits(3) = op_code[23 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  op2 : bits(3) = op_code[4 .. 2];
  LL : bits(2) = op_code[1 .. 0];
  system_exceptions_runtime_svc_decode(opc, imm16, op2, LL)
}

function clause decode (0b1101011 @ _ : bits(1) @ 0b0 @ _ : bits(2) @ 0b111110000 @ _ : bits(12) as op_code) = {
  Z : bits(1) = [op_code[24]];
  opc : bits(1) = [op_code[23]];
  op : bits(2) = op_code[22 .. 21];
  op2 : bits(5) = op_code[20 .. 16];
  op3 : bits(4) = op_code[15 .. 12];
  A : bits(1) = [op_code[11]];
  M : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  Rm : bits(5) = op_code[4 .. 0];
  branch_unconditional_register_decode(Z, opc, op, op2, op3, A, M, Rn, Rm)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(8) @ 0b10000000 @ _ : bits(5) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  imm8 : bits(8) = op_code[20 .. 13];
  imm5 : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_move_fp_imm_decode(M, S, typ, imm8, imm5, Rd)
}

function clause decode (_ : bits(1) @ 0b011011 @ _ : bits(25) as op_code) = {
  b5 : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[24]];
  b40 : bits(5) = op_code[23 .. 19];
  imm14 : bits(14) = op_code[18 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  branch_conditional_test_decode(b5, op, b40, imm14, Rt)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_postidx_aarch64_memory_single_general_immediate_signed_postidx__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_preidx_aarch64_memory_single_general_immediate_signed_postidx__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111001 @ _ : bits(24) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_signed_postidx__decode(size, V, opc, imm12, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b011000 @ _ : bits(24) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  imm19 : bits(19) = op_code[23 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_literal_general_decode(opc, V, imm19, Rt)
}

function clause decode (_ : bits(2) @ 0b1011001 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_simdfp_postidx_aarch64_memory_pair_simdfp_postidx__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b1011011 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_simdfp_preidx_aarch64_memory_pair_simdfp_postidx__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b1011010 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_simdfp_offset_aarch64_memory_pair_simdfp_postidx__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (_ : bits(1) @ 0b011010 @ _ : bits(25) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[24]];
  imm19 : bits(19) = op_code[23 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  branch_conditional_compare_decode(sf, op, imm19, Rt)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_simdfp_immediate_signed_offset_normal_aarch64_memory_single_simdfp_immediate_signed_offset_normal__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b001 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_pacib_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  integer_pac_pacib_hint_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_simdfp_immediate_signed_postidx_aarch64_memory_single_simdfp_immediate_signed_postidx__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_simdfp_immediate_signed_preidx_aarch64_memory_single_simdfp_immediate_signed_postidx__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111101 @ _ : bits(24) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_simdfp_immediate_unsigned_aarch64_memory_single_simdfp_immediate_signed_postidx__decode(size, V, opc, imm12, Rn, Rt)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011000 @ _ : bits(1) @ 0b000000 @ _ : bits(16) as op_code) = {
  Q : bits(1) = [op_code[30]];
  L : bits(1) = [op_code[22]];
  opcode : bits(4) = op_code[15 .. 12];
  size : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_vector_multiple_nowb_aarch64_memory_vector_multiple_nowb__decode(Q, L, opcode, size, Rn, Rt)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011001 @ _ : bits(1) @ 0b0 @ _ : bits(21) as op_code) = {
  Q : bits(1) = [op_code[30]];
  L : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode : bits(4) = op_code[15 .. 12];
  size : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_vector_multiple_postinc_aarch64_memory_vector_multiple_nowb__decode(Q, L, Rm, opcode, size, Rn, Rt)
}

function clause decode (0b11010110100111110000 @ _ : bits(12) as op_code) = {
  opc : bits(4) = op_code[24 .. 21];
  op2 : bits(5) = op_code[20 .. 16];
  op3 : bits(4) = op_code[15 .. 12];
  A : bits(1) = [op_code[11]];
  M : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  op4 : bits(5) = op_code[4 .. 0];
  branch_unconditional_eret_decode(opc, op2, op3, A, M, Rn, op4)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b01 @ _ : bits(2) @ 0b10 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(2) = op_code[13 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_maxmin_decode(M, S, typ, Rm, op, Rn, Rd)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b10000 @ _ : bits(2) @ 0b10000 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  opc : bits(2) = op_code[16 .. 15];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_unary_decode(M, S, typ, opc, Rn, Rd)
}

function clause decode (0b11010100000 @ _ : bits(16) @ 0b00011 as op_code) = {
  opc : bits(3) = op_code[23 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  op2 : bits(3) = op_code[4 .. 2];
  LL : bits(2) = op_code[1 .. 0];
  system_exceptions_runtime_smc_decode(opc, imm16, op2, LL)
}

function clause decode (_ : bits(2) @ 0b0010001 @ _ : bits(1) @ 0b0 @ _ : bits(21) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  o2 : bits(1) = [op_code[23]];
  L : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[21]];
  Rs : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_ordered_decode(size, o2, L, o1, Rs, o0, Rt2, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  option_name : bits(3) = op_code[15 .. 13];
  S : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_register_aarch64_memory_single_general_register__decode(size, V, opc, Rm, option_name, S, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b1011000 @ _ : bits(23) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  L : bits(1) = [op_code[22]];
  imm7 : bits(7) = op_code[21 .. 15];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_pair_simdfp_noalloc_aarch64_memory_pair_simdfp_noalloc__decode(opc, V, L, imm7, Rt2, Rn, Rt)
}

function clause decode (0b11010100001 @ _ : bits(16) @ 0b00000 as op_code) = {
  opc : bits(3) = op_code[23 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  op2 : bits(3) = op_code[4 .. 2];
  LL : bits(2) = op_code[1 .. 0];
  system_exceptions_debug_breakpoint_decode(opc, imm16, op2, LL)
}

function clause decode (_ : bits(1) @ 0b0011011000 @ _ : bits(21) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op54 : bits(2) = op_code[30 .. 29];
  op31 : bits(3) = op_code[23 .. 21];
  Rm : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_mul_uniform_addsub_decode(sf, op54, op31, Rm, o0, Ra, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b011100 @ _ : bits(24) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  imm19 : bits(19) = op_code[23 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_literal_simdfp_decode(opc, V, imm19, Rt)
}

function clause decode (0b1101010100 @ _ : bits(1) @ 0b01 @ _ : bits(19) as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  system_sysops_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (_ : bits(3) @ 0b01011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  shift : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  imm6 : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_addsub_shiftedreg_decode(sf, op, S, shift, Rm, imm6, Rn, Rd)
}

function clause decode (_ : bits(3) @ 0b100100 @ _ : bits(23) as op_code) = {
  sf : bits(1) = [op_code[31]];
  opc : bits(2) = op_code[30 .. 29];
  N : bits(1) = [op_code[22]];
  immr : bits(6) = op_code[21 .. 16];
  imms : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_logical_immediate_decode(sf, opc, N, immr, imms, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111010010 @ _ : bits(9) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  cond : bits(4) = op_code[15 .. 12];
  o2 : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  o3 : bits(1) = [op_code[4]];
  nzcv : bits(4) = op_code[3 .. 0];
  integer_conditional_compare_register_decode(sf, op, S, Rm, cond, o2, Rn, o3, nzcv)
}

function clause decode (_ : bits(3) @ 0b100110 @ _ : bits(23) as op_code) = {
  sf : bits(1) = [op_code[31]];
  opc : bits(2) = op_code[30 .. 29];
  N : bits(1) = [op_code[22]];
  immr : bits(6) = op_code[21 .. 16];
  imms : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_bitfield_decode(sf, opc, N, immr, imms, Rn, Rd)
}

function clause decode (0b1101010100 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) = {
  L : bits(1) = [op_code[21]];
  o0 : bits(1) = [op_code[19]];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  system_register_system_decode(L, o0, op1, CRn, CRm, op2, Rt)
}

function clause decode (_ : bits(2) @ 0b111010010 @ _ : bits(9) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  cond : bits(4) = op_code[15 .. 12];
  o2 : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  o3 : bits(1) = [op_code[4]];
  nzcv : bits(4) = op_code[3 .. 0];
  integer_conditional_compare_immediate_decode(sf, op, S, imm5, cond, o2, Rn, o3, nzcv)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000110 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_div_decode(M, S, typ, Rm, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  A : bits(1) = [op_code[23]];
  R : bits(1) = [op_code[22]];
  Rs : bits(5) = op_code[20 .. 16];
  o3 : bits(1) = [op_code[15]];
  opc : bits(3) = op_code[14 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_atomicops_swp_decode(size, V, A, R, Rs, o3, opc, Rn, Rt)
}

function clause decode (_ : bits(3) @ 0b10001 @ _ : bits(24) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  shift : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_addsub_immediate_decode(sf, op, S, shift, imm12, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b00101 @ _ : bits(26) as op_code) = {
  op : bits(1) = [op_code[31]];
  imm26 : bits(26) = op_code[25 .. 0];
  branch_unconditional_immediate_decode(op, imm26)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b110 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_autda_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b10110101100000000010 @ _ : bits(11) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_cnt_decode(sf, S, opcode2, op, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111 @ _ : bits(1) @ 0b00 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b00 @ _ : bits(5) @ 0b11111 as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  A : bits(1) = [op_code[23]];
  R : bits(1) = [op_code[22]];
  Rs : bits(5) = op_code[20 .. 16];
  o3 : bits(1) = [op_code[15]];
  opc : bits(3) = op_code[14 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_atomicops_st_decode(size, V, A, R, Rs, o3, opc, Rn, Rt)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b1 @ _ : bits(2) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  opc : bits(2) = op_code[6 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  system_barriers_decode(L, op0, op1, CRn, CRm, opc, Rt)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0010000 @ _ : bits(1) @ 0b1 @ _ : bits(21) as op_code) = {
  sz : bits(1) = [op_code[30]];
  o2 : bits(1) = [op_code[23]];
  L : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[21]];
  Rs : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_atomicops_cas_pair_decode(sz, o2, L, o1, Rs, o0, Rt2, Rn, Rt)
}

function clause decode (_ : bits(3) @ 0b100101 @ _ : bits(23) as op_code) = {
  sf : bits(1) = [op_code[31]];
  opc : bits(2) = op_code[30 .. 29];
  hw : bits(2) = op_code[22 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_insext_insert_movewide_decode(sf, opc, hw, imm16, Rd)
}

function clause decode (0b11010110101111110000001111100000 as op_code) = {
  opc : bits(4) = op_code[24 .. 21];
  op2 : bits(5) = op_code[20 .. 16];
  op3 : bits(6) = op_code[15 .. 10];
  Rt : bits(5) = op_code[9 .. 5];
  op4 : bits(5) = op_code[4 .. 0];
  branch_unconditional_dret_decode(opc, op2, op3, Rt, op4)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  cond : bits(4) = op_code[15 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_move_fp_select_decode(M, S, typ, Rm, cond, Rn, Rd)
}

function clause decode (0b11010100101 @ _ : bits(16) @ 0b000 @ _ : bits(2) as op_code) = {
  opc : bits(3) = op_code[23 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  op2 : bits(3) = op_code[4 .. 2];
  LL : bits(2) = op_code[1 .. 0];
  system_exceptions_debug_exception_decode(opc, imm16, op2, LL)
}

function clause decode (_ : bits(1) @ 0b1011010110000000000 @ _ : bits(12) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  opc : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_rev_decode(sf, S, opcode2, opc, Rn, Rd)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b10001 @ _ : bits(2) @ 0b10000 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  opc : bits(2) = op_code[16 .. 15];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_convert_fp_decode(M, S, typ, opc, Rn, Rd)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b000 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_pacia_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  integer_pac_pacia_hint_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  rmode : bits(2) = op_code[20 .. 19];
  opcode : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_convert_int_decode(sf, S, typ, rmode, opcode, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b011010100 @ _ : bits(9) @ 0b0 @ _ : bits(11) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  cond : bits(4) = op_code[15 .. 12];
  o2 : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_conditional_select_decode(sf, op, S, Rm, cond, o2, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  A : bits(1) = [op_code[23]];
  R : bits(1) = [op_code[22]];
  Rs : bits(5) = op_code[20 .. 16];
  o3 : bits(1) = [op_code[15]];
  opc : bits(3) = op_code[14 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_orderedrcpc_decode(size, V, A, R, Rs, o3, opc, Rn, Rt)
}

function clause decode (_ : bits(3) @ 0b01011001 @ _ : bits(21) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  opt : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  option_name : bits(3) = op_code[15 .. 13];
  imm3 : bits(3) = op_code[12 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_addsub_extendedreg_decode(sf, op, S, opt, Rm, option_name, imm3, Rn, Rd)
}

function clause decode (_ : bits(3) @ 0b10000 @ _ : bits(24) as op_code) = {
  op : bits(1) = [op_code[31]];
  immlo : bits(2) = op_code[30 .. 29];
  immhi : bits(19) = op_code[23 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_address_pcrel_decode(op, immlo, immhi, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011010 @ _ : bits(2) @ 0b00000 @ _ : bits(16) as op_code) = {
  Q : bits(1) = [op_code[30]];
  L : bits(1) = [op_code[22]];
  R : bits(1) = [op_code[21]];
  opcode : bits(3) = op_code[15 .. 13];
  S : bits(1) = [op_code[12]];
  size : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_vector_single_nowb_aarch64_memory_vector_single_nowb__decode(Q, L, R, opcode, S, size, Rn, Rt)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011011 @ _ : bits(23) as op_code) = {
  Q : bits(1) = [op_code[30]];
  L : bits(1) = [op_code[22]];
  R : bits(1) = [op_code[21]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode : bits(3) = op_code[15 .. 13];
  S : bits(1) = [op_code[12]];
  size : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_vector_single_postinc_aarch64_memory_vector_single_nowb__decode(Q, L, R, Rm, opcode, S, size, Rn, Rt)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(10) @ 0b1 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  M : bits(1) = [op_code[23]];
  S : bits(1) = [op_code[22]];
  imm9 : bits(9) = op_code[20 .. 12];
  W : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_pac_decode(size, V, M, S, imm9, W, Rn, Rt)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b101 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_autib_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  integer_pac_autib_hint_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  cond : bits(4) = op_code[15 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  op : bits(1) = [op_code[4]];
  nzcv : bits(4) = op_code[3 .. 0];
  float_compare_cond_decode(M, S, typ, Rm, cond, Rn, op, nzcv)
}

function clause decode (_ : bits(2) @ 0b0010000 @ _ : bits(1) @ 0b0 @ _ : bits(21) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  o2 : bits(1) = [op_code[23]];
  L : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[21]];
  Rs : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Rt2 : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_exclusive_single_decode(size, o2, L, o1, Rs, o0, Rt2, Rn, Rt)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  rmode : bits(2) = op_code[20 .. 19];
  opcode : bits(3) = op_code[18 .. 16];
  scale : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_convert_fix_decode(sf, S, typ, rmode, opcode, scale, Rn, Rd)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1001 @ _ : bits(3) @ 0b10000 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  rmode : bits(3) = op_code[17 .. 15];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_round_decode(M, S, typ, rmode, Rn, Rd)
}

function clause decode (_ : bits(3) @ 0b01010 @ _ : bits(24) as op_code) = {
  sf : bits(1) = [op_code[31]];
  opc : bits(2) = op_code[30 .. 29];
  shift : bits(2) = op_code[23 .. 22];
  N : bits(1) = [op_code[21]];
  Rm : bits(5) = op_code[20 .. 16];
  imm6 : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_logical_shiftedreg_decode(sf, opc, shift, N, Rm, imm6, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b010 @ _ : bits(13) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode2 : bits(3) = op_code[15 .. 13];
  C : bits(1) = [op_code[12]];
  sz : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_crc_decode(sf, op, S, Rm, opcode2, C, sz, Rn, Rd)
}

function clause decode (_ : bits(3) @ 0b11010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode2 : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_addsub_carry_decode(sf, op, S, Rm, opcode2, Rn, Rd)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(7) @ 0b000 as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(2) = op_code[15 .. 14];
  Rn : bits(5) = op_code[9 .. 5];
  opc : bits(2) = op_code[4 .. 3];
  float_compare_uncond_decode(M, S, typ, Rm, op, Rn, opc)
}

function clause decode (0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) = {
  L : bits(1) = [op_code[21]];
  op0 : bits(2) = op_code[20 .. 19];
  op1 : bits(3) = op_code[18 .. 16];
  CRn : bits(4) = op_code[15 .. 12];
  CRm : bits(4) = op_code[11 .. 8];
  op2 : bits(3) = op_code[7 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  system_hints_decode(L, op0, op1, CRn, CRm, op2, Rt)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b0010 @ _ : bits(12) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode2 : bits(4) = op_code[15 .. 12];
  op2 : bits(2) = op_code[11 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_shift_variable_decode(sf, op, S, Rm, opcode2, op2, Rn, Rd)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b011 @ _ : bits(10) as op_code) = {
  sf : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  opcode2 : bits(5) = op_code[20 .. 16];
  Z : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_pac_pacdb_dp_1src_decode(sf, S, opcode2, Z, Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_offset_unpriv_aarch64_memory_single_general_immediate_signed_offset_unpriv__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  M : bits(1) = [op_code[31]];
  S : bits(1) = [op_code[29]];
  typ : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  float_arithmetic_addsub_decode(M, S, typ, Rm, op, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b00100111 @ _ : bits(1) @ 0b0 @ _ : bits(21) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op21 : bits(2) = op_code[30 .. 29];
  N : bits(1) = [op_code[22]];
  o0 : bits(1) = [op_code[21]];
  Rm : bits(5) = op_code[20 .. 16];
  imms : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_insext_extract_immediate_decode(sf, op21, N, o0, Rm, imms, Rn, Rd)
}

function clause decode (0b11010100010 @ _ : bits(16) @ 0b00000 as op_code) = {
  opc : bits(3) = op_code[23 .. 21];
  imm16 : bits(16) = op_code[20 .. 5];
  op2 : bits(3) = op_code[4 .. 2];
  LL : bits(2) = op_code[1 .. 0];
  system_exceptions_debug_halt_decode(opc, imm16, op2, LL)
}

function clause decode (0b10011011 @ _ : bits(1) @ 0b01 @ _ : bits(21) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op54 : bits(2) = op_code[30 .. 29];
  U : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  o0 : bits(1) = [op_code[15]];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_mul_widening_3264_decode(sf, op54, U, Rm, o0, Ra, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b00001 @ _ : bits(11) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  Rm : bits(5) = op_code[20 .. 16];
  opcode2 : bits(5) = op_code[15 .. 11];
  o1 : bits(1) = [op_code[10]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_div_decode(sf, op, S, Rm, opcode2, o1, Rn, Rd)
}
