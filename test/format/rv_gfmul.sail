// =======================================================================================
// This test is derived from the sail-riscv model. See RISCV_LICENSE in the formatting
// tests directory.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

function gfmul(x : bits(8), y : bits(4)) -> bits(8) = {
  (if bit_to_bool(y[0]) then             x    else 0x00) ^
  (if bit_to_bool(y[1]) then xt2(        x)   else 0x00) ^
  (if bit_to_bool(y[2]) then xt2(xt2(    x))  else 0x00) ^
  (if bit_to_bool(y[3]) then xt2(xt2(xt2(x))) else 0x00)
}

overload operator ^^^ = operator ^

function gfmul(x : bits(8), y : bits(4)) -> bits(8) = {
  (if bit_to_bool(y[0]) then             x    else 0x00) ^
  (if bit_to_bool(y[1]) then xt2(        x)   else 0x00) ^^^
  (if bit_to_bool(y[2]) then xt2(xt2(    x))  else 0x00) ^
  (if bit_to_bool(y[3]) then xt2(xt2(xt2(x))) else 0x00)
}

$[fmt skip]
function gfmul(x : bits(8), y : bits(4)) -> bits(8) = {
  (if bit_to_bool(y[0]) then             x    else 0x00) ^
  (if bit_to_bool(y[1]) then xt2(        x)   else 0x00) ^
  (if bit_to_bool(y[2]) then xt2(xt2(    x))  else 0x00) ^
  (if bit_to_bool(y[3]) then xt2(xt2(xt2(x))) else 0x00)
}
