// =======================================================================================
// This test is derived from the sail-riscv model. See RISCV_LICENSE in the formatting
// tests directory.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// num_elem means max(VLMAX,VLEN/SEW)) according to Section 5.4 of RVV spec
function get_num_elem(LMUL_pow : int, SEW : sew_bitsize) -> nat1 = {
    let LMUL_pow_reg = if LMUL_pow < 0 then { 0 } else { LMUL_pow };

    // Ignore lmul < 1 so that the entire vreg is read, allowing all masking to
    // be handled in init_masked_result
    let num_elem = (2 ^ LMUL_pow_reg) * vlen / SEW;
    assert(num_elem > 0);
    num_elem
}
