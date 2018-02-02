function clause decode _ : bits(2) @ 0b111001 @ _ : bits(24) as op_code = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_unsigned__decode(size, V, opc, imm12, Rn, Rt)
}

function clause decode _ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_postidx_aarch64_memory_single_general_immediate_signed_postidx__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode _ : bits(2) @ 0b111000 @ _ : bits(2) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm9 : bits(9) = op_code[20 .. 12];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_signed_preidx_aarch64_memory_single_general_immediate_signed_postidx__decode(size, V, opc, imm9, Rn, Rt)
}

function clause decode _ : bits(2) @ 0b111001 @ _ : bits(24) as op_code = {
  size : bits(2) = op_code[31 .. 30];
  V : bits(1) = [op_code[26]];
  opc : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rt : bits(5) = op_code[4 .. 0];
  memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_signed_postidx__decode(size, V, opc, imm12, Rn, Rt)
}

function clause decode _ : bits(3) @ 0b10001 @ _ : bits(24) as op_code = {
  sf : bits(1) = [op_code[31]];
  op : bits(1) = [op_code[30]];
  S : bits(1) = [op_code[29]];
  shift : bits(2) = op_code[23 .. 22];
  imm12 : bits(12) = op_code[21 .. 10];
  Rn : bits(5) = op_code[9 .. 5];
  Rd : bits(5) = op_code[4 .. 0];
  integer_arithmetic_addsub_immediate_decode(sf, op, S, shift, imm12, Rn, Rd)
}
