default Order dec

$include <prelude.sail>

/* Type-level `if`, `div` and `mod` used as operands of arithmetic. Backends
   that print these without parentheses can silently compute the wrong value
   (e.g. Lean parses `if c then 8 else 4 * 8` as `if c then 8 else (4 * 8)`). */

type ext_d_supported : Bool = true
type flen_bytes : Int = if ext_d_supported then 8 else 4
type flen : Int = flen_bytes * 8

type sum_if : Int = 1 + (if ext_d_supported then 2 else 3)
type pow_if : Int = 2 ^ (if ext_d_supported then 3 else 4) * 2
type mul_div : Int = 2 * div(7, 2)
type mul_mod : Int = 2 * mod(7, 4)

val main : unit -> unit

/* Each value's type goes through the type synonym, so the generated code has
   to evaluate the type-level expression itself. In the Lean backend, a width
   mismatch is silently fixed by a coercion (BitVec.setWidth), so the wrong
   width only becomes visible at runtime through length(). */
function main() = {
  let a : bits(flen) = sail_zeros(sizeof(flen));
  let b : bits(sum_if) = sail_zeros(sizeof(sum_if));
  let c : bits(pow_if) = sail_zeros(sizeof(pow_if));
  let d : bits(mul_div) = sail_zeros(sizeof(mul_div));
  let e : bits(mul_mod) = sail_zeros(sizeof(mul_mod));
  print_endline(dec_str(length(a)));
  print_endline(dec_str(length(b)));
  print_endline(dec_str(length(c)));
  print_endline(dec_str(length(d)));
  print_endline(dec_str(length(e)));
}
