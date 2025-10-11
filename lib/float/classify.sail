$ifndef _FLOAT_CLASSIFY
$define _FLOAT_CLASSIFY

$include <float/common.sail>
$include <float/nan.sail>
$include <float/zero.sail>
$include <float/normal.sail>
$include <float/inf.sail>
$include <float/sign.sail>

// Classify floating point numbers into one of these classes. All floating point
// numbers are in exactly one class.
enum float_class = {
  float_class_negative_inf,
  float_class_negative_normal,
  float_class_negative_subnormal,
  float_class_negative_zero,
  float_class_positive_zero,
  float_class_positive_subnormal,
  float_class_positive_normal,
  float_class_positive_inf,
  float_class_snan,
  float_class_qnan,
}

// Classify a floating point number into exactly one of the 10 possible classes.
function float_classify(f : fp_bits) -> float_class =
  if      float_is_snan(f)      then float_class_snan
  else if float_is_qnan(f)      then float_class_qnan
  else if float_is_zero(f)      then (if float_is_positive(f) then float_class_positive_zero      else float_class_negative_zero)
  else if float_is_subnormal(f) then (if float_is_positive(f) then float_class_positive_subnormal else float_class_negative_subnormal)
  else if float_is_normal(f)    then (if float_is_positive(f) then float_class_positive_normal    else float_class_negative_normal)
  else if float_is_inf(f)       then (if float_is_positive(f) then float_class_positive_inf       else float_class_negative_inf)
  else {
    // This is unreachable.
    assert(false, "float_classify internal logic error");
    undefined
  }

$endif
