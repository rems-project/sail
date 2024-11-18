/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_DATA
$define _FLOAT_DATA

/* Half floating point */
let fp16_pos_snan_0      = 0x7c01
let fp16_pos_snan_1      = 0x7d10
let fp16_neg_snan_0      = 0xfc01
let fp16_neg_snan_1      = 0xfd10

let fp16_pos_qnan_0       = 0x7e00
let fp16_pos_qnan_1       = 0x7e01
let fp16_pos_qnan_default = 0x7e00
let fp16_neg_qnan_0       = 0xfe00
let fp16_neg_qnan_1       = 0xfe01
let fp16_neg_qnan_default = 0xfe00

let fp16_pos_inf         = 0x7c00
let fp16_neg_inf         = 0xfc00

let fp16_pos_zero        = 0x0000
let fp16_neg_zero        = 0x8000

let fp16_pos_denormal_0  = 0x0200
let fp16_pos_denormal_1  = 0x02f0
let fp16_neg_denormal_0  = 0x8200
let fp16_neg_denormal_1  = 0x82f0

let fp16_pos_normal_0    = 0x7a00
let fp16_pos_normal_1    = 0x71ff
let fp16_neg_normal_0    = 0xfa00
let fp16_neg_normal_1    = 0xf1ff

let fp16_pos_denormal_add_0_op_0 = 0x00ff
let fp16_pos_denormal_add_0_op_1 = 0x0021
let fp16_pos_denormal_add_0_sum  = 0x0120

let fp16_pos_denormal_add_1_op_0 = 0x03ff
let fp16_pos_denormal_add_1_op_1 = 0x0002
let fp16_pos_denormal_add_1_sum  = 0x0401

let fp16_neg_denormal_add_0_op_0 = 0x80ff
let fp16_neg_denormal_add_0_op_1 = 0x8021
let fp16_neg_denormal_add_0_sum  = 0x8120

let fp16_neg_denormal_add_1_op_0 = 0x83ff
let fp16_neg_denormal_add_1_op_1 = 0x8002
let fp16_neg_denormal_add_1_sum  = 0x8401

/* Single floating point */
let fp32_pos_snan_0      = 0x7f800001
let fp32_pos_snan_1      = 0x7f8f0000
let fp32_neg_snan_0      = 0xff800001
let fp32_neg_snan_1      = 0xff8f0000

let fp32_pos_qnan_0       = 0x7fc00000
let fp32_pos_qnan_1       = 0x7fc00001
let fp32_pos_qnan_default = 0x7fc00000
let fp32_neg_qnan_0       = 0xffc00000
let fp32_neg_qnan_1       = 0xffc00001
let fp32_neg_qnan_default = 0xffc00000

let fp32_pos_inf         = 0x7f800000
let fp32_neg_inf         = 0xff800000

let fp32_pos_zero        = 0x00000000
let fp32_neg_zero        = 0x80000000

let fp32_pos_denormal_0  = 0x00700000
let fp32_pos_denormal_1  = 0x0010ff01
let fp32_neg_denormal_0  = 0x80700000
let fp32_neg_denormal_1  = 0x8010ff01

let fp32_pos_normal_0    = 0x1a000000
let fp32_pos_normal_1    = 0x0100002f
let fp32_neg_normal_0    = 0x9a000000
let fp32_neg_normal_1    = 0x8100002f

let fp32_pos_denormal_add_0_op_0 = 0x000fffff
let fp32_pos_denormal_add_0_op_1 = 0x00000021
let fp32_pos_denormal_add_0_sum  = 0x00100020

let fp32_pos_denormal_add_1_op_0 = 0x007fffff
let fp32_pos_denormal_add_1_op_1 = 0x00000002
let fp32_pos_denormal_add_1_sum  = 0x00800001

let fp32_neg_denormal_add_0_op_0 = 0x800fffff
let fp32_neg_denormal_add_0_op_1 = 0x80000021
let fp32_neg_denormal_add_0_sum  = 0x80100020

let fp32_neg_denormal_add_1_op_0 = 0x807fffff
let fp32_neg_denormal_add_1_op_1 = 0x80000002
let fp32_neg_denormal_add_1_sum  = 0x80800001

/* Double floating point */
let fp64_pos_snan_0      = 0x7ff0000000000001
let fp64_pos_snan_1      = 0x7ff7000000000000
let fp64_neg_snan_0      = 0xfff0000000000001
let fp64_neg_snan_1      = 0xfff7000000000000

let fp64_pos_qnan_0       = 0x7ff8000000000000
let fp64_pos_qnan_1       = 0x7fff000000000000
let fp64_pos_qnan_default = 0x7ff8000000000000
let fp64_neg_qnan_0       = 0xfff8000000000000
let fp64_neg_qnan_1       = 0xffff000000000000
let fp64_neg_qnan_default = 0xfff8000000000000

let fp64_pos_inf         = 0x7ff0000000000000
let fp64_neg_inf         = 0xfff0000000000000

let fp64_pos_zero        = 0x0000000000000000
let fp64_neg_zero        = 0x8000000000000000

let fp64_pos_denormal_0  = 0x000f000000000000
let fp64_pos_denormal_1  = 0x0000000fff000000
let fp64_neg_denormal_0  = 0x800f000000000000
let fp64_neg_denormal_1  = 0x8000000fff000000

let fp64_pos_normal_0    = 0x1000000000000000
let fp64_pos_normal_1    = 0x0100001111000000
let fp64_neg_normal_0    = 0x9000000000000000
let fp64_neg_normal_1    = 0x8100001111000000

let fp64_pos_denormal_add_0_op_0 = 0x0000ffffffffffff
let fp64_pos_denormal_add_0_op_1 = 0x0000000000000041
let fp64_pos_denormal_add_0_sum  = 0x0001000000000040

let fp64_pos_denormal_add_1_op_0 = 0x000fffffffffffff
let fp64_pos_denormal_add_1_op_1 = 0x0000000000000002
let fp64_pos_denormal_add_1_sum  = 0x0010000000000001

let fp64_neg_denormal_add_0_op_0 = 0x8000ffffffffffff
let fp64_neg_denormal_add_0_op_1 = 0x8000000000000041
let fp64_neg_denormal_add_0_sum  = 0x8001000000000040

let fp64_neg_denormal_add_1_op_0 = 0x800fffffffffffff
let fp64_neg_denormal_add_1_op_1 = 0x8000000000000002
let fp64_neg_denormal_add_1_sum  = 0x8010000000000001

/* Quad floating point */
let fp128_pos_snan_0     = 0x7fff0000000000000000000000000001
let fp128_pos_snan_1     = 0x7fff000000000000ff00000000000000
let fp128_neg_snan_0     = 0xffff0000000000000000000000000001
let fp128_neg_snan_1     = 0xffff000000000000ff00000000000000

let fp128_pos_qnan_0       = 0x7fff8000000000000000000000000001
let fp128_pos_qnan_1       = 0x7fff8d00000000000000000000000000
let fp128_pos_qnan_default = 0x7fff8000000000000000000000000000
let fp128_neg_qnan_0       = 0xffff8000000000000000000000000001
let fp128_neg_qnan_1       = 0xffff8d00000000000000000000000000
let fp128_neg_qnan_default = 0xffff8000000000000000000000000000

let fp128_pos_inf        = 0x7fff0000000000000000000000000000
let fp128_neg_inf        = 0xffff0000000000000000000000000000

let fp128_pos_zero       = 0x00000000000000000000000000000000
let fp128_neg_zero       = 0x80000000000000000000000000000000

let fp128_pos_denormal_0 = 0x0000f000000000000000000000000000
let fp128_pos_denormal_1 = 0x0000000fff0000000000000000000000
let fp128_neg_denormal_0 = 0x8000f000000000000000000000000000
let fp128_neg_denormal_1 = 0x8000000fff0000000000000000000000

let fp128_pos_normal_0   = 0x10000000000000000000000000000000
let fp128_pos_normal_1   = 0x01000011110000000000000000000000
let fp128_neg_normal_0   = 0x90000000000000000000000000000000
let fp128_neg_normal_1   = 0x81000011110000000000000000000000

let fp128_pos_denormal_add_0_op_0 = 0x00000fffffffffffffffffffffffffff
let fp128_pos_denormal_add_0_op_1 = 0x00000000000000000000000000000091
let fp128_pos_denormal_add_0_sum  = 0x00001000000000000000000000000090

let fp128_pos_denormal_add_1_op_0 = 0x0000ffffffffffffffffffffffffffff
let fp128_pos_denormal_add_1_op_1 = 0x00000000000000000000000000000003
let fp128_pos_denormal_add_1_sum  = 0x00010000000000000000000000000002

let fp128_neg_denormal_add_0_op_0 = 0x80000fffffffffffffffffffffffffff
let fp128_neg_denormal_add_0_op_1 = 0x80000000000000000000000000000091
let fp128_neg_denormal_add_0_sum  = 0x80001000000000000000000000000090

let fp128_neg_denormal_add_1_op_0 = 0x8000ffffffffffffffffffffffffffff
let fp128_neg_denormal_add_1_op_1 = 0x80000000000000000000000000000003
let fp128_neg_denormal_add_1_sum  = 0x80010000000000000000000000000002

$endif
