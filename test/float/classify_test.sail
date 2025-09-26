default Order dec

$include <prelude.sail>
$include <generic_equality.sail>
$include <float/classify.sail>
$include "data.sail"

function test_float_classify () -> unit = {
  /* Half floating point */
  assert(float_classify(fp16_pos_snan_0) == float_class_snan);
  assert(float_classify(fp16_pos_snan_1) == float_class_snan);
  assert(float_classify(fp16_neg_snan_0) == float_class_snan);
  assert(float_classify(fp16_neg_snan_1) == float_class_snan);

  assert(float_classify(fp16_pos_qnan_0) == float_class_qnan);
  assert(float_classify(fp16_pos_qnan_1) == float_class_qnan);
  assert(float_classify(fp16_neg_qnan_0) == float_class_qnan);
  assert(float_classify(fp16_neg_qnan_1) == float_class_qnan);

  assert(float_classify(fp16_pos_inf) == float_class_positive_inf);
  assert(float_classify(fp16_neg_inf) == float_class_negative_inf);

  assert(float_classify(fp16_pos_zero) == float_class_positive_zero);
  assert(float_classify(fp16_neg_zero) == float_class_negative_zero);

  assert(float_classify(fp16_pos_subnormal_0) == float_class_positive_subnormal);
  assert(float_classify(fp16_pos_subnormal_1) == float_class_positive_subnormal);
  assert(float_classify(fp16_neg_subnormal_0) == float_class_negative_subnormal);
  assert(float_classify(fp16_neg_subnormal_1) == float_class_negative_subnormal);

  assert(float_classify(fp16_pos_normal_0) == float_class_positive_normal);
  assert(float_classify(fp16_pos_normal_1) == float_class_positive_normal);
  assert(float_classify(fp16_neg_normal_0) == float_class_negative_normal);
  assert(float_classify(fp16_neg_normal_1) == float_class_negative_normal);

  /* Single floating point */
  assert(float_classify(fp32_pos_snan_0) == float_class_snan);
  assert(float_classify(fp32_pos_snan_1) == float_class_snan);
  assert(float_classify(fp32_neg_snan_0) == float_class_snan);
  assert(float_classify(fp32_neg_snan_1) == float_class_snan);

  assert(float_classify(fp32_pos_qnan_0) == float_class_qnan);
  assert(float_classify(fp32_pos_qnan_1) == float_class_qnan);
  assert(float_classify(fp32_neg_qnan_0) == float_class_qnan);
  assert(float_classify(fp32_neg_qnan_1) == float_class_qnan);

  assert(float_classify(fp32_pos_inf) == float_class_positive_inf);
  assert(float_classify(fp32_neg_inf) == float_class_negative_inf);

  assert(float_classify(fp32_pos_zero) == float_class_positive_zero);
  assert(float_classify(fp32_neg_zero) == float_class_negative_zero);

  assert(float_classify(fp32_pos_subnormal_0) == float_class_positive_subnormal);
  assert(float_classify(fp32_pos_subnormal_1) == float_class_positive_subnormal);
  assert(float_classify(fp32_neg_subnormal_0) == float_class_negative_subnormal);
  assert(float_classify(fp32_neg_subnormal_1) == float_class_negative_subnormal);

  assert(float_classify(fp32_pos_normal_0) == float_class_positive_normal);
  assert(float_classify(fp32_pos_normal_1) == float_class_positive_normal);
  assert(float_classify(fp32_neg_normal_0) == float_class_negative_normal);
  assert(float_classify(fp32_neg_normal_1) == float_class_negative_normal);

  /* Double floating point */
  assert(float_classify(fp64_pos_snan_0) == float_class_snan);
  assert(float_classify(fp64_pos_snan_1) == float_class_snan);
  assert(float_classify(fp64_neg_snan_0) == float_class_snan);
  assert(float_classify(fp64_neg_snan_1) == float_class_snan);

  assert(float_classify(fp64_pos_qnan_0) == float_class_qnan);
  assert(float_classify(fp64_pos_qnan_1) == float_class_qnan);
  assert(float_classify(fp64_neg_qnan_0) == float_class_qnan);
  assert(float_classify(fp64_neg_qnan_1) == float_class_qnan);

  assert(float_classify(fp64_pos_inf) == float_class_positive_inf);
  assert(float_classify(fp64_neg_inf) == float_class_negative_inf);

  assert(float_classify(fp64_pos_zero) == float_class_positive_zero);
  assert(float_classify(fp64_neg_zero) == float_class_negative_zero);

  assert(float_classify(fp64_pos_subnormal_0) == float_class_positive_subnormal);
  assert(float_classify(fp64_pos_subnormal_1) == float_class_positive_subnormal);
  assert(float_classify(fp64_neg_subnormal_0) == float_class_negative_subnormal);
  assert(float_classify(fp64_neg_subnormal_1) == float_class_negative_subnormal);

  assert(float_classify(fp64_pos_normal_0) == float_class_positive_normal);
  assert(float_classify(fp64_pos_normal_1) == float_class_positive_normal);
  assert(float_classify(fp64_neg_normal_0) == float_class_negative_normal);
  assert(float_classify(fp64_neg_normal_1) == float_class_negative_normal);

  /* Quad floating point */
  assert(float_classify(fp128_pos_snan_0) == float_class_snan);
  assert(float_classify(fp128_pos_snan_1) == float_class_snan);
  assert(float_classify(fp128_neg_snan_0) == float_class_snan);
  assert(float_classify(fp128_neg_snan_1) == float_class_snan);

  assert(float_classify(fp128_pos_qnan_0) == float_class_qnan);
  assert(float_classify(fp128_pos_qnan_1) == float_class_qnan);
  assert(float_classify(fp128_neg_qnan_0) == float_class_qnan);
  assert(float_classify(fp128_neg_qnan_1) == float_class_qnan);

  assert(float_classify(fp128_pos_inf) == float_class_positive_inf);
  assert(float_classify(fp128_neg_inf) == float_class_negative_inf);

  assert(float_classify(fp128_pos_zero) == float_class_positive_zero);
  assert(float_classify(fp128_neg_zero) == float_class_negative_zero);

  assert(float_classify(fp128_pos_subnormal_0) == float_class_positive_subnormal);
  assert(float_classify(fp128_pos_subnormal_1) == float_class_positive_subnormal);
  assert(float_classify(fp128_neg_subnormal_0) == float_class_negative_subnormal);
  assert(float_classify(fp128_neg_subnormal_1) == float_class_negative_subnormal);

  assert(float_classify(fp128_pos_normal_0) == float_class_positive_normal);
  assert(float_classify(fp128_pos_normal_1) == float_class_positive_normal);
  assert(float_classify(fp128_neg_normal_0) == float_class_negative_normal);
  assert(float_classify(fp128_neg_normal_1) == float_class_negative_normal);
}

function main () -> unit = {
  test_float_classify();
}
