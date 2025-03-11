function f b = if b == bitone then bitzero else bitone

function f b = if b == bitone then { bitzero } else { bitone }

function f b = if b == bitone then { let a = 1;bitzero } else { bitone }

function f b = if b == bitone then {  {bitzero } } else { bitone }

function f b = if b == bitone then {  {{bitzero} } } else { bitone }

function f b = if b == bitone then { { let a = 1; bitzero } } else { bitone }

function f b = if b == bitone then { { {let a = 1; bitzero} } } else { bitone }

function f b = if b == bitone then { { { {let a = 1; bitzero}} } } else { {{{let a= 1; bitone}}} }

function f b = if b == bitone then { { { {let a = 1; bitzero}} } } else { {{bitone }}}

function f b = if b == bitone then { { { {let a = 1; bitzero}} } } else { {let a = 1;{bitone }}}

 /* comment */
function/* comment */f b = if b == bitone then bitzero else bitone

function f/* comment */b = if b == bitone then bitzero else bitone

function f b/* comment */= if b == bitone then bitzero else bitone

function f b = /* comment */if b == bitone then bitzero else bitone

// TODO function f b =/* comment */if b == bitone then bitzero else bitone

function f b = if/* comment */b == bitone then bitzero else bitone

function f b = if b/* comment */== bitone then bitzero else bitone

function f b = if b == /* comment */ bitone then bitzero else bitone

// TODO function f b = if b ==/* comment */bitone then bitzero else bitone

function f b = if b == bitone/* comment */then bitzero else bitone

function f b = if b == bitone then/* comment */bitzero else bitone

function f b = if b == bitone then bitzero/* comment */else bitone

function f b = if b == bitone then bitzero else/* comment */bitone

function f b = if b == bitone then bitzero else bitone/* comment */

function hex_bits_signed_forwards bv = {
  if signed(bv) < 0 then {
    (length(bv), concat_str("-", hex_str(unsigned(not_vec(bv) + 1))))
  } else {
    (length(bv), hex_str(unsigned(bv)))
  }
}

function valid_hex_bits_signed(n, str) = {
  if string_take(str_make_this_line_wider_than_120, 1) == "-" then { valid_hex_bits(n, string_drop(str, 1))} else { valid_hex_bits(n, str)}
}

function if_stmt () =
    if let a = 1 in a
    then { // comment
        2
    } else { app(1, x)[1..2] }

val fp_min : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bits('m)
function fp_min(op1, op2) = {
  let (fflags, op1_lt_op2) : (bits_fflags, bool) = match sizeof('m) {
    16 => riscv_f16Lt_quiet(op1, op2),
    32 => riscv_f32Lt_quiet(op1, op2),
    64 => riscv_f64Lt_quiet(op1, op2),
  };

  let result_val = if f_is_NaN(op1) & f_is_NaN(op2) then {
    canonical_NaN(sizeof('m))
  } else {
    if f_is_NaN(op1) then {
      op2
    } else {
      if f_is_NaN(op2) then {
        op1
      } else {
        if f_is_neg_zero(op1) & f_is_pos_zero(op2) then {
          op1
        } else {
          if f_is_neg_zero(op2) & f_is_pos_zero(op1) then {
            op2
          } else {
            if op1_lt_op2 then {
              op1
            } else {
              /* (not rs2_lt_rs1) */ op2
            }
          }
        }
      }
    }
  };
  accrue_fflags(fflags);
  result_val
}
