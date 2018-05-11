function clause decode (0b011111110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_leftinsert_sisd_decode(U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_leftinsert_simd_decode(Q, U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_int_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode(U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_narrow_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0110 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_maxmin_single_decode(Q, U, size, Rm, o1, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_saturating_sisd_decode(U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_saturating_simd_decode(Q, U, size, Rm, Rn, Rd)
}

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

function clause decode (0b01111111 @ _ : bits(8) @ 0b11 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  S : bits(1) = [op_code[13]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_high_sisd_decode(U, size, L, M, Rm, S, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b11 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  S : bits(1) = [op_code[13]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_high_simd_decode(Q, U, size, L, M, Rm, S, H, Rn, Rd)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110100 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_double_sisd_decode(U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110100 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_double_simd_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(1) @ 0b10 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp16_fused_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  op : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp_fused_decode(Q, U, op, sz, Rm, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_diffneg_int_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_diffneg_int_simd_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b11001110011 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3_rax1_decode(Rm, O, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_halving_truncating_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(1) @ 0b10 @ _ : bits(5) @ 0b0010 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  E : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  ac : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(U, E, Rm, ac, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b1110 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  E : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  ac : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(U, E, sz, Rm, ac, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(1) @ 0b10 @ _ : bits(5) @ 0b0010 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  E : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  ac : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Q, U, E, Rm, ac, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b1110 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  E : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  ac : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_fp_simd_decode(Q, U, E, sz, Rm, ac, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b0 @ _ : bits(1) @ 0b1110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_permute_zip_decode(Q, size, Rm, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01111 @ _ : bits(8) @ 0b1110 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_dotp_decode(Q, U, size, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010 @ _ : bits(2) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  R : bits(1) = [op_code[12]];
  S : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_shift_sisd_decode(U, size, Rm, R, S, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010 @ _ : bits(2) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  R : bits(1) = [op_code[12]];
  S : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_shift_simd_decode(Q, U, size, Rm, R, S, Rn, Rd)
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

function clause decode (0b01 @ _ : bits(1) @ 0b1111001111001110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_conv_int_sisd_decode(U, a, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_conv_int_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111001111001110110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_conv_int_simd_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_conv_int_simd_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b11001110001 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
  Op0 : bits(2) = op_code[22 .. 21];
  Rm : bits(5) = op_code[20 .. 16];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3_bcax_decode(Op0, Rm, Ra, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b0 @ _ : bits(1) @ 0b1010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_permute_transpose_decode(Q, size, Rm, op, Rn, Rd)
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

function clause decode (0b01 @ _ : bits(1) @ 0b111110 @ _ : bits(7) @ 0b00 @ _ : bits(2) @ 0b01 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  o1 : bits(1) = [op_code[13]];
  o0 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_right_sisd_decode(U, immh, immb, o1, o0, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011110 @ _ : bits(7) @ 0b00 @ _ : bits(2) @ 0b01 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  o1 : bits(1) = [op_code[13]];
  o0 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_right_simd_decode(Q, U, immh, immb, o1, o0, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(1) @ 0b1111001101 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  o2 : bits(1) = [op_code[23]];
  o1 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(U, o2, o1, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b100001101 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  o2 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(U, o2, sz, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(1) @ 0b1111001101 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o2 : bits(1) = [op_code[23]];
  o1 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Q, U, o2, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100001101 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o2 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Q, U, o2, sz, o1, Rn, Rd)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3op_sha256sched1_decode(size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001111110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrtfp16_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001111110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrt_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b01011110110 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode(U, a, Rm, Rn, Rd)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_rsqrts_sisd_decode(U, sz, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_rsqrts_simd_decode(Q, U, sz, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100000 @ _ : bits(3) @ 0b111111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[18]];
  b : bits(1) = [op_code[17]];
  c : bits(1) = [op_code[16]];
  cmode : bits(4) = op_code[15 .. 12];
  o2 : bits(1) = [op_code[11]];
  d : bits(1) = [op_code[9]];
  e : bits(1) = [op_code[8]];
  f : bits(1) = [op_code[7]];
  g : bits(1) = [op_code[6]];
  h : bits(1) = [op_code[5]];
  Rd : bits(5) = op_code[4 .. 0];
  vector_fp16_movi_decode(Q, op, a, b, c, cmode, o2, d, e, f, g, h, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111100000 @ _ : bits(7) @ 0b01 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[18]];
  b : bits(1) = [op_code[17]];
  c : bits(1) = [op_code[16]];
  cmode : bits(4) = op_code[15 .. 12];
  o2 : bits(1) = [op_code[11]];
  d : bits(1) = [op_code[9]];
  e : bits(1) = [op_code[8]];
  f : bits(1) = [op_code[7]];
  g : bits(1) = [op_code[6]];
  h : bits(1) = [op_code[5]];
  Rd : bits(5) = op_code[4 .. 0];
  vector_logical_decode(Q, op, a, b, c, cmode, o2, d, e, f, g, h, Rd)
}

function clause decode (0b01011111 @ _ : bits(8) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_double_sisd_decode(U, size, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_double_simd_decode(Q, U, size, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrtest_int_decode(Q, U, sz, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(1) @ 0b10 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Op3 : bits(3) = op_code[13 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Q, U, a, Rm, Op3, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_maxmin_fp_2008_decode(Q, U, o1, sz, Rm, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_conv_float_sisd_decode(U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_conv_float_simd_decode(Q, U, immh, immb, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001011110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_widen_decode(Q, U, sz, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_integer_move_unsigned_decode(Q, op, imm5, imm4, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b00 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_addsub_wide_decode(Q, U, size, Rm, o1, Rn, Rd)
}

function clause decode (0b0101111100 @ _ : bits(6) @ 0b0 @ _ : bits(1) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_fp16_sisd_decode(U, size, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b010111111 @ _ : bits(7) @ 0b0 @ _ : bits(1) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_fp_sisd_decode(U, sz, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b0 @ _ : bits(1) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_fp16_simd_decode(Q, U, size, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0 @ _ : bits(1) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_fp_simd_decode(Q, U, sz, L, M, Rm, o2, H, Rn, Rd)
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

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_saturating_sisd_decode(U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_saturating_simd_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1000 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_int_decode(Q, U, size, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011110 @ _ : bits(7) @ 0b101001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_leftlong_decode(Q, U, immh, immb, Rn, Rd)
}

function clause decode (0b11001110010 @ _ : bits(5) @ 0b10 @ _ : bits(2) @ 0b11 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  imm2 : bits(2) = op_code[13 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3tt2b_decode(Rm, imm2, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110000 @ _ : bits(5) @ 0b0 @ _ : bits(4) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op2 : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_extract_decode(Q, op2, Rm, imm4, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_extract_sat_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_extract_sat_simd_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b11001110011 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3partw2_decode(Rm, O, Rn, Rd)
}

function clause decode (0b0101111011111001110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_recip_fp16_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_recip_float_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111001110110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_recip_fp16_simd_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_recip_float_simd_decode(Q, U, sz, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(1) @ 0b10 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Q, U, o1, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_maxmin_fp_1985_decode(Q, U, o1, sz, Rm, Rn, Rd)
}

function clause decode (0b11001110011 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha512_sha512h2_decode(Rm, O, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111000100000010110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_not_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b0101111011111000111010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_fp16_lessthan_sisd_decode(U, a, Rn, Rd)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100000111010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_float_lessthan_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111000111010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000111010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_float_lessthan_simd_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b01010100 @ _ : bits(19) @ 0b0 @ _ : bits(4) as op_code) = {
  o1 : bits(1) = [op_code[24]];
  imm19 : bits(19) = op_code[23 .. 5];
  o0 : bits(1) = [op_code[4]];
  cond : bits(4) = op_code[3 .. 0];
  branch_conditional_cond_decode(o1, imm19, o0, cond)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001100000010110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_rbit_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b01011110000 @ _ : bits(5) @ 0b010 @ _ : bits(1) @ 0b00 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  P : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3op_sha256hash_decode(size, Rm, P, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b110000001110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_addlong_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b11001110010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
  Op0 : bits(2) = op_code[22 .. 21];
  Rm : bits(5) = op_code[20 .. 16];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3ss1_decode(Op0, Rm, Ra, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_halving_rounding_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode(U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b1100111011000000100000 @ _ : bits(10) as op_code) = {
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha512_sha512su0_decode(Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b0 @ _ : bits(3) @ 0b00 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op2 : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  len : bits(2) = op_code[14 .. 13];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_table_decode(Q, op2, Rm, len, op, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode(U, size, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b0100111000101000010 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  D : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_aes_round_decode(size, D, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b100000100 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_int_bulk_sisd_decode(U, size, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100000100 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_int_bulk_simd_decode(Q, U, size, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_wrapping_pair_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b01 @ _ : bits(1) @ 0b000 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_addsub_narrow_decode(Q, U, size, Rm, o1, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b011011 @ _ : bits(25) as op_code) = {
  b5 : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[24]];
  b40 : bits(5) = op_code[23 .. 19];
  imm14 : bits(14) = op_code[18 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  branch_conditional_test_decode(b5, op, b40, imm14, Rt)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111011111000111110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_diffneg_fp16_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011101 @ _ : bits(1) @ 0b100000111110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_diffneg_float_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b111000 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_poly_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_int_decode(Q, U, size, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001001110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_shift_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  opc2 : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_logical_bsleor_decode(Q, U, opc2, Rm, Rn, Rd)
}

function clause decode (0b1100111011000000100001 @ _ : bits(10) as op_code) = {
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm4_sm4enc_decode(Rn, Rd)
}

function clause decode (_ : bits(2) @ 0b011000 @ _ : bits(24) as op_code) = {
  opc : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  imm19 : bits(19) = op_code[23 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_literal_general_decode(opc, V, imm19, Rt)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_integer_move_signed_decode(Q, op, imm5, imm4, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000010110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cnt_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3op_sha1sched0_decode(size, Rm, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b011010 @ _ : bits(25) as op_code) = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[24]];
  imm19 : bits(19) = op_code[23 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  branch_conditional_compare_decode(sf, op, imm19, Rt)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_integer_dup_decode(Q, op, imm5, imm4, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110010 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_fp16_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_fp_decode(Q, U, sz, Rm, Rn, Rd)
}

function clause decode (0b11001110011 @ _ : bits(5) @ 0b110010 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm4_sm4enckey_decode(Rm, O, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b1111001111001110010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111001111001110010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_conv_float_tieaway_simd_decode(Q, U, sz, Rn, Rd)
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

function clause decode (0b01011110 @ _ : bits(2) @ 0b110000110010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fp16maxnm_sisd_decode(U, o1, sz, Rn, Rd)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b110000110010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fpmaxnm_sisd_decode(U, o1, sz, Rn, Rd)
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

function clause decode (0b01011110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode(U, a, Rm, Rn, Rd)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode(U, sz, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode(Q, U, sz, Rm, Rn, Rd)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3op_sha1hash_majority_decode(size, Rm, Rn, Rd)
}

function clause decode (0b11001110011 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3partw1_decode(Rm, O, Rn, Rd)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_left_sisd_decode(U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_left_simd_decode(Q, U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_recip_int_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_dotp_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b11001110010 @ _ : bits(5) @ 0b10 @ _ : bits(2) @ 0b01 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  imm2 : bits(2) = op_code[13 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3tt1b_decode(Rm, imm2, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b1000 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightnarrow_logical_decode(Q, U, immh, immb, op, Rn, Rd)
}

function clause decode (0b0101111000101000001010 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha2op_sha256sched0_decode(size, Rn, Rd)
}

function clause decode (0b01111110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_fp16_sisd_decode(U, a, Rm, Rn, Rd)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_fp_sisd_decode(U, sz, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_fp16_simd_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_fp_simd_decode(Q, U, sz, Rm, Rn, Rd)
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

function clause decode (0b01011111 @ _ : bits(8) @ 0b110 @ _ : bits(2) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  op : bits(1) = [op_code[12]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_high_sisd_decode(U, size, L, M, Rm, op, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b110 @ _ : bits(2) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  op : bits(1) = [op_code[12]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_high_simd_decode(Q, U, size, L, M, Rm, op, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0111 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  ac : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_diff_decode(Q, U, size, Rm, ac, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b1111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_fp16_sisd_decode(U, size, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_fp_sisd_decode(U, sz, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_fp16_simd_decode(Q, U, size, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_fp_simd_decode(Q, U, sz, L, M, Rm, H, Rn, Rd)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b110001101110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_add_sisd_decode(U, size, Rn, Rd)
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

function clause decode (0b0100111000101000011 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  D : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_aes_mix_decode(size, D, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_product_decode(Q, U, size, Rm, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_conv_int_sisd_decode(U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_conv_int_simd_decode(Q, U, immh, immb, Rn, Rd)
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

function clause decode (0b01111110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_extract_sqxtun_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_extract_sqxtun_simd_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b110000110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fp16add_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b110000110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fpadd_sisd_decode(U, sz, Rn, Rd)
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

function clause decode (0b011111100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_xtn_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_xtn_simd_decode(Q, U, sz, Rn, Rd)
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

function clause decode (0b11001110100 @ _ : bits(21) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  imm6 : bits(6) = op_code[15 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3_xar_decode(Rm, imm6, Rn, Rd)
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

function clause decode (0b01011110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_recpsfp16_sisd_decode(U, a, Rm, Rn, Rd)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_recps_sisd_decode(U, sz, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_recpsfp16_simd_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_recps_simd_decode(Q, U, sz, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(1) @ 0b1111001100 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o2 : bits(1) = [op_code[23]];
  o1 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_fp16_round_decode(Q, U, o2, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100001100 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o2 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  o1 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_float_round_decode(Q, U, o2, sz, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_divfp16_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_div_decode(Q, U, sz, Rm, Rn, Rd)
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

function clause decode (0b11001110010 @ _ : bits(5) @ 0b10 @ _ : bits(2) @ 0b10 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  imm2 : bits(2) = op_code[13 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3tt2a_decode(Rm, imm2, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1000000 @ _ : bits(1) @ 0b1010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  op : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_add_pairwise_decode(Q, U, size, op, Rn, Rd)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_cpydup_sisd_decode(op, imm5, imm4, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_cpydup_simd_decode(Q, op, imm5, imm4, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b11000 @ _ : bits(1) @ 0b101010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  op : bits(1) = [op_code[16]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_intmax_decode(Q, U, size, op, Rn, Rd)
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

function clause decode (0b0111111011111001110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode(U, a, Rn, Rd)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrtest_float_sisd_decode(U, sz, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001110110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrtest_fp16_simd_decode(Q, U, a, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_sqrtest_float_simd_decode(Q, U, sz, Rn, Rd)
}

function clause decode (0b11001110011 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha512_sha512h_decode(Rm, O, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100000000 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  o0 : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_rev_decode(Q, U, size, o0, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b00 @ _ : bits(1) @ 0b000 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_addsub_long_decode(Q, U, size, Rm, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b0 @ _ : bits(1) @ 0b0110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_permute_unzip_decode(Q, size, Rm, op, Rn, Rd)
}

function clause decode (_ : bits(1) @ 0b00101 @ _ : bits(26) as op_code) = {
  op : bits(1) = [op_code[31]];
  imm26 : bits(26) = op_code[25 .. 0];
  branch_unconditional_immediate_decode(op, imm26)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b111 @ _ : bits(1) @ 0b01 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  rot : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_add_fp_complex_decode(Q, U, size, Rm, rot, Rn, Rd)
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

function clause decode (0b0101111000101000000010 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha2op_sha1hash_decode(size, Rn, Rd)
}

function clause decode (0b01001110000 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_integer_insert_decode(Q, op, imm5, imm4, Rn, Rd)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b110000111110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fp16max_sisd_decode(U, o1, sz, Rn, Rd)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b110000111110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fpmax_sisd_decode(U, o1, sz, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0011 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  eq : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_int_sisd_decode(U, size, Rm, eq, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0011 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  eq : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_cmp_int_simd_decode(Q, U, size, Rm, eq, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_product_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b11001110000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
  Op0 : bits(2) = op_code[22 .. 21];
  Rm : bits(5) = op_code[20 .. 16];
  Ra : bits(5) = op_code[14 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3_eor3_decode(Op0, Rm, Ra, Rn, Rd)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b010001 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightinsert_sisd_decode(U, immh, immb, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b010001 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightinsert_simd_decode(Q, U, immh, immb, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_diffneg_sat_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_diffneg_sat_simd_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b01011111 @ _ : bits(8) @ 0b0 @ _ : bits(1) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_double_sisd_decode(U, size, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0 @ _ : bits(1) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_double_simd_decode(Q, U, size, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111110 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightnarrow_uniform_sisd_decode(U, immh, immb, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011110 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightnarrow_uniform_simd_decode(Q, U, immh, immb, op, Rn, Rd)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3op_sha1hash_choose_decode(size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp16_product_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp_product_decode(Q, U, sz, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_logical_andorr_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b01111110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b1000 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  S : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode(U, size, Rm, S, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b1000 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  S : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode(Q, U, size, Rm, S, Rn, Rd)
}

function clause decode (0b11001110010 @ _ : bits(5) @ 0b10 @ _ : bits(2) @ 0b00 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  imm2 : bits(2) = op_code[13 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sm3_sm3tt1a_decode(Rm, imm2, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b000 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_accum_decode(Q, U, size, Rm, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b110 @ _ : bits(2) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  rot : bits(2) = op_code[12 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_fp_complex_decode(Q, U, size, Rm, rot, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  rot : bits(2) = op_code[14 .. 13];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_complex_decode(Q, U, size, L, M, Rm, rot, H, Rn, Rd)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode(U, size, Rm, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_mul_dmacc_simd_decode(Q, U, size, Rm, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110001101110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_add_simd_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b01 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  op : bits(1) = [op_code[13]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_disparate_diff_decode(Q, U, size, Rm, op, Rn, Rd)
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

function clause decode (0b0101111011111001111110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_frecpxfp16_decode(U, a, Rn, Rd)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100001111110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_special_frecpx_decode(U, sz, Rn, Rd)
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

function clause decode (0b01011110000 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha3op_sha1hash_parity_decode(size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_mul_int_accum_decode(Q, U, size, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(1) @ 0b0110000110010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fp16maxnm_simd_decode(Q, U, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110000110010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fpmaxnm_simd_decode(Q, U, o1, sz, Rn, Rd)
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

function clause decode (0b11001110011 @ _ : bits(5) @ 0b100010 @ _ : bits(10) as op_code) = {
  Rm : bits(5) = op_code[20 .. 16];
  O : bits(1) = [op_code[14]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha512_sha512su1_decode(Rm, O, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01111 @ _ : bits(8) @ 0b1010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mul_long_decode(Q, U, size, L, M, Rm, H, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100000010010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_clsz_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01111 @ _ : bits(8) @ 0b0 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  L : bits(1) = [op_code[21]];
  M : bits(1) = [op_code[20]];
  Rm : bits(4) = op_code[19 .. 16];
  o2 : bits(1) = [op_code[14]];
  H : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_element_mulacc_long_decode(Q, U, size, L, M, Rm, o2, H, Rn, Rd)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b1000 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightnarrow_nonuniform_sisd_decode(U, immh, immb, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b1000 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_rightnarrow_nonuniform_simd_decode(Q, U, immh, immb, op, Rn, Rd)
}

function clause decode (0b01101110000 @ _ : bits(5) @ 0b0 @ _ : bits(4) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  imm5 : bits(5) = op_code[20 .. 16];
  imm4 : bits(4) = op_code[14 .. 11];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_transfer_vector_insert_decode(Q, op, imm5, imm4, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_extract_nosat_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111100000 @ _ : bits(7) @ 0b01 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  op : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[18]];
  b : bits(1) = [op_code[17]];
  c : bits(1) = [op_code[16]];
  cmode : bits(4) = op_code[15 .. 12];
  o2 : bits(1) = [op_code[11]];
  d : bits(1) = [op_code[9]];
  e : bits(1) = [op_code[8]];
  f : bits(1) = [op_code[7]];
  g : bits(1) = [op_code[6]];
  h : bits(1) = [op_code[5]];
  Rd : bits(5) = op_code[4 .. 0];
  vector_logical_decode(Q, op, a, b, c, cmode, o2, d, e, f, g, h, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111110 @ _ : bits(7) @ 0b011 @ _ : bits(1) @ 0b01 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_leftsat_sisd_decode(U, immh, immb, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011110 @ _ : bits(7) @ 0b011 @ _ : bits(1) @ 0b01 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  immh : bits(4) = op_code[22 .. 19];
  immb : bits(3) = op_code[18 .. 16];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_shift_leftsat_simd_decode(Q, U, immh, immb, op, Rn, Rd)
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

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000101010 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_int_lessthan_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000101010 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_int_lessthan_simd_decode(Q, U, size, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b1111011111000110 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(U, a, op, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b111101 @ _ : bits(1) @ 0b100000110 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_float_bulk_sisd_decode(U, sz, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111011111000110 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Q, U, a, op, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011101 @ _ : bits(1) @ 0b100000110 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  op : bits(1) = [op_code[12]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_cmp_float_bulk_simd_decode(Q, U, sz, op, Rn, Rd)
}

function clause decode (0b0101111000101000000110 @ _ : bits(10) as op_code) = {
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_crypto_sha2op_sha1sched1_decode(size, Rn, Rd)
}

function clause decode (0b01 @ _ : bits(1) @ 0b11110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) = {
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_add_saturating_sisd_decode(U, size, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_unary_add_saturating_simd_decode(Q, U, size, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b1010 @ _ : bits(1) @ 0b1 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  size : bits(2) = op_code[23 .. 22];
  Rm : bits(5) = op_code[20 .. 16];
  o1 : bits(1) = [op_code[11]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_maxmin_pair_decode(Q, U, size, Rm, o1, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(2) @ 0b01110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  a : bits(1) = [op_code[23]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_fp16_simd_decode(Q, U, a, Rm, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  sz : bits(1) = [op_code[22]];
  Rm : bits(5) = op_code[20 .. 16];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_arithmetic_binary_uniform_sub_fp_simd_decode(Q, U, sz, Rm, Rn, Rd)
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

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(1) @ 0b0110000111110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fp16max_simd_decode(Q, U, o1, Rn, Rd)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110000111110 @ _ : bits(10) as op_code) = {
  Q : bits(1) = [op_code[30]];
  U : bits(1) = [op_code[29]];
  o1 : bits(1) = [op_code[23]];
  sz : bits(1) = [op_code[22]];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  vector_reduce_fpmax_simd_decode(Q, U, o1, sz, Rn, Rd)
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
