default Order inc

scattered typedef ast = const union
val ast -> unit effect pure execute
scattered function unit execute

union ast member (unit) DUMMY
function clause execute (DUMMY) = ()

end ast
end execute

(*val extern string -> unit effect {wmv} printt*)

function unit test_assert (name, pred) = {
  print (name);
  if pred then
    print (": pass\n")
  else
    print(": fail\n")
}

function unit test_not () = {
  test_assert ("not_bit0", (not (bitzero)) == bitone);
  test_assert ("not_bit1", (not (bitone)) == bitzero);

  test_assert ("bitwise_not", (~ (0b01) == 0b10));
  test_assert ("bitwise_not_bit0", (~ (bitzero) == bitone));
  test_assert ("bitwise_not_bit1", (~ (bitone) == bitzero));
}

function unit test_or () = {
  test_assert ("bitwise_or", (0b0101 | 0b0011) == 0b0111);
  test_assert ("bitwise_or_00", (bitzero | bitzero) == bitzero);
  test_assert ("bitwise_or_01", (bitzero | bitone)  == bitone);
  test_assert ("bitwise_or_10", (bitone  | bitzero) == bitone);
  test_assert ("bitwise_or_11", (bitone  | bitone)  == bitone);
}

function unit test_xor () = {
  test_assert ("bitwise_xor", (0b0101 ^ 0b0011) == 0b0110);
  test_assert ("bitwise_xor_00", (bitzero ^ bitzero) == bitzero);
  test_assert ("bitwise_xor_01", (bitzero ^ bitone)  == bitone);
  test_assert ("bitwise_xor_10", (bitone  ^ bitzero) == bitone);
  test_assert ("bitwise_xor_11", (bitone  ^ bitone)  == bitzero);
}

function unit test_and () = {
  test_assert ("bitwise_and", (0b0101 & 0b0011) == 0b0001);
  test_assert ("bitwise_and_00", (bitzero & bitzero) == bitzero);
  test_assert ("bitwise_and_01", (bitzero & bitone)  == bitzero);
  test_assert ("bitwise_and_10", (bitone  & bitzero) == bitzero);
  test_assert ("bitwise_and_11", (bitone  & bitone)  == bitone);
}

function unit test_leftshift () = {
  test_assert ("leftshift_small0", (0x99 << 0) == 0x99);
  test_assert ("leftshift_small3", (0x99 << 3) == 0xc8);
  test_assert ("leftshift_small7", (0x99 << 7) == 0x80);
  test_assert ("leftshift_small8", (0x99 << 8) == 0x00);
  test_assert ("leftshift_big0", (0x99999999999999999 << 0) == 0x99999999999999999);
  test_assert ("leftshift_big3", (0x99999999999999999 << 3) == 0xcccccccccccccccc8);
  test_assert ("leftshift_big7", (0x99999999999999999 << 7) == 0xccccccccccccccc80);
  test_assert ("leftshift_big68", (0x99999999999999999 << 68) == 0x00000000000000000);
}

function unit test_rightshift () = {
  test_assert ("rightshift_small0", (0x99 >> 0) == 0x99);
  test_assert ("rightshift_small3", (0x99 >> 3) == 0x13);
  test_assert ("rightshift_small7", (0x99 >> 7) == 0x01);
  test_assert ("rightshift_small8", (0x99 >> 8) == 0x00); (* XXX fails on interp *)
  test_assert ("rightshift_big0", (0x99999999999999999 >> 0) == 0x99999999999999999);
  test_assert ("rightshift_big3", (0x99999999999999999 >> 3) == 0x13333333333333333);
  test_assert ("rightshift_big7", (0x99999999999999999 >> 7) == 0x01333333333333333);
  test_assert ("rightshift_big68", (0x99999999999999999 >> 68) == 0x00000000000000000); (* XXX fails on interp *)
}

function unit test_rotate () = { 
  test_assert ("rotate0", (0x99 <<< 0) == 0x99); (* XXX fails on interp *)
  test_assert ("rotate3", (0x99 <<< 3) == 0xcc);
  test_assert ("rotate7", (0x99 <<< 7) == 0xcc);
  test_assert ("rotate8", (0x99 <<< 8) == 0x99);
}

function unit test_duplicate () = {
  (* XXX crashes on shallow embedding
  should type have a constraint n>0?
  test_assert ("duplicate_empty", (bitzero ^^ 0) == []); *)
  test_assert ("duplicate0", (bitzero ^^ 8) == 0x00);
  test_assert ("duplicate1", (bitone ^^ 8) == 0xff);

  (* XXX crashes on shallow embedding 
  test_assert ("duplicate_bits0", (0x21 ^^ 0) == []);*)
  test_assert ("duplicate_bits1", (0xce ^^ 1) == 0xce);
  test_assert ("duplicate_bits9", (0xce ^^ 9) == 0xcecececececececece);
  test_assert ("duplicate_covfefe", (0xc0 : (0xfe ^^ 2)) == 0xc0fefe);
}

function unit test_ext () = {
  test_assert ("extz0", EXTZ(0b00) == 0x00);
  test_assert ("extz1", EXTZ(0b10) == 0x02);
  test_assert ("extz2", EXTZ(0b10) == 0b10);
  test_assert ("extz3", EXTZ(0b10) == 0b0);
  
  test_assert ("exts0", EXTS(0b00) == 0x00);
  test_assert ("exts1", EXTS(0b10) == 0xfe);
  test_assert ("exts2", EXTS(0b10) == 0b10);
  test_assert ("exts3", EXTS(0b10) == 0b0);

  test_assert ("most_significant0", most_significant(0b011) == bitzero);
  test_assert ("most_significant1", most_significant(0b100) == bitone);
  }

function unit test_add () = {
  test_assert ("add", 1 + 1 == 2);
  test_assert ("add_vec", ((bit[4])(0x1 + 0x1)) == 0x2);
  test_assert ("add_vec_ov", ((bit[4])(0xf + 0x1)) == 0x0);
  test_assert ("add_vec_vec_range", ((range<0,30>)(0x1 + 0x1)) == 2);
  test_assert ("add_vec_vec_range_ov", ((range<0,15>)(0xf + 0x1)) == 0); (* XXX broken... *)
  test_assert ("add_vec_range", ((bit[4])(0x1 + 1)) == 0x2);
  test_assert ("add_vec_range_range", ((range<0,15>)(0xe + 1)) == 15);
  test_assert ("add_overflow_vec", (((bit[4], bit, bit))(0x1 + 0x1)) == (0x2, false, false));
  test_assert ("add_overflow_vec_ov", (((bit[4], bit, bit))(0xf + 0x1)) == (0x0, true, true)); (* XXX overflow flag makes no sense for unsigned... *)
  test_assert ("add_overflow_vec_ovs", (((bit[4], bit, bit))(0x4 + 0x4)) == (0x8, false, false));
  test_assert ("add_vec_range_range", ((range<0,16>)(0xe + 1)) == 15);
  test_assert ("add_range_vec", ((bit[4])(1 + 0xe)) == 0xf);
  test_assert ("add_range_vec_range", ((range<0,3>)(1 + 0xe)) == 15);
  test_assert ("add_vec_bit", ((bit[4])(0xe + bitone)) == 0xf);
  (* not defined on either model...
  test_assert ("add_bit_vec", ((bit[4])(bitone + 0x1)) == 0x2); *)
}

function unit test_add_signed() = {
  test_assert ("adds", 1 +_s 1 == 2); (* same as unsigned *)
  test_assert ("adds_vec", ((bit[4])(0x1 +_s 0x1)) == 0x2);  (* same as unsigned *)
  test_assert ("adds_vec_ov", ((bit[4])(0xf +_s 0x1)) == 0x0);  (* same as unsigned *)

  (* XXX would be good to restrict range type *)
  test_assert ("adds_vec_vec_range_pp", ((int)(0x1 +_s 0x1)) == 2);
  test_assert ("adds_vec_vec_range_np", ((int)(0xa +_s 0x1)) == (-5));
  test_assert ("adds_vec_vec_range_pn", ((int)(0x3 +_s 0xe)) == 1);
  test_assert ("adds_vec_vec_range_nn", ((int)(0x8 +_s 0x8)) == (-16));

  test_assert ("adds_vec_range", ((bit[4])(0xe +_s 1)) == 0xf);
  test_assert ("adds_vec_range_range", ((int)(0xe +_s 1)) == (-1));
  (* returns (result, signed overflow, carry out)*)
  test_assert ("adds_overflow_vec0", (((bit[4], bit, bit))(0x1 +_s 0x1)) == (0x2, false, false));
  test_assert ("adds_overflow_vec1", (((bit[4], bit, bit))(0xf +_s 0x1)) == (0x0, false, true));
  test_assert ("adds_overflow_vec2", (((bit[4], bit, bit))(0x7 +_s 0x1)) == (0x8, true, false));
  test_assert ("adds_overflow_vec3", (((bit[4], bit, bit))(0x8 +_s 0x8)) == (0x0, true, true));

  test_assert ("adds_vec_range_range", ((int)(0xe +_s 1)) == (-1));
  test_assert ("adds_range_vec", ((bit[4])(1 +_s 0xe)) == 0xf);
  test_assert ("adds_range_vec_range", ((int)(1 +_s 0xe)) == -1);
  test_assert ("adds_vec_bit", ((bit[4])(0xe +_s bitone)) == 0xf);
  (* not defined on either model... 
  test_assert ("adds_bit_vec", ((bit[4])(bitone +_s 0xe)) == 0xf);*)
}

function unit test_minus() = {
  test_assert("minus", 1 - 1 == 0);
  test_assert("minus_vec", ((bit[4])(0x2 - 0x1)) == 0x1);
  test_assert("minus_vec_ov", ((bit[4])(0x1 - 0xf)) == 0x2);
  (* XXX minus_vec_vec_range not implemented 
  test_assert("minus_vec_vec_range_pp", ((int)(0x1 - 0x1)) == 0);
  test_assert("minus_vec_vec_range_np", ((int)(0xa - 0x1)) == 9);
  test_assert("minus_vec_vec_range_pn", ((int)(0x3 - 0xe)) == 5);
  test_assert("minus_vec_vec_range_nn", ((int)(0x8 - 0x8)) == 0);*)
  test_assert("minus_vec_range", ((bit[4])(0xe - 1)) == 0xd);
  test_assert("minus_vec_range_range", ((int)(0xe - 1)) == 13);
  test_assert("minus_range_vec", ((bit[4])(1 - 0xe)) == 0x3);
  test_assert("minus_range_vec_range", ((int)(1 - 0xe)) == -13);
  (* returns (result, signed overflow, borrow in)*)
  test_assert ("minus_overflow_vec0", (((bit[4], bit, bit))(0x1 - 0x1)) == (0x0, false, false));
  test_assert ("minus_overflow_vec1", (((bit[4], bit, bit))(0x0 - 0x1)) == (0xf, true, true));
  test_assert ("minus_overflow_vec2", (((bit[4], bit, bit))(0x8 - 0x1)) == (0x7, false, false));
  test_assert ("minus_overflow_vec3", (((bit[4], bit, bit))(0x0 - 0x8)) == (0x8, true, true));

  test_assert ("minus_overflow_vec_bit0", (((bit[4], bit, bit))(0x1 - bitone)) == (0x0, false, false));
  test_assert ("minus_overflow_vec_bit1", (((bit[4], bit, bit))(0x0 - bitone)) == (0xf, true, true));
  test_assert ("minus_overflow_vec_bit2", (((bit[4], bit, bit))(0x8 - bitone)) == (0x7, false, false));
  test_assert ("minus_overflow_vec_bit3", (((bit[4], bit, bit))(0x8 - bitzero)) == (0x8, false, false)); (* XXX shallow embedding returns true, false... *)
}

function unit test_minus_signed() = {
  test_assert("minus_signed", 1 -_s 1 == 0);
  (* XXX minus_vec_signed not implemented
  test_assert("minus_vec_signed", ((bit[4])(0x2 -_s 0x1)) == 0x1); 
  test_assert("minus_vec_ov_signed", ((bit[4])(0x1 -_s 0xf)) == 0x2); *)
  (* XXX minus_vec_vec_range_signed not implemented 
  test_assert("minus_vec_vec_range_signed_pp", ((int)(0x1 -_s 0x1)) == 0);
  test_assert("minus_vec_vec_range_signed_np", ((int)(0xa -_s 0x1)) == 9);
  test_assert("minus_vec_vec_range_signed_pn", ((int)(0x3 -_s 0xe)) == 5);
  test_assert("minus_vec_vec_range_signed_nn", ((int)(0x8 -_s 0x8)) == 0);*)
  (* XXX not implemented 
  test_assert("minus_vec_range_signed", ((bit[4])(0xe -_s 1)) == 0xd);
  test_assert("minus_vec_range_range_signed", ((int)(0xe -_s 1)) == -3);
  test_assert("minus_range_vec_signed", ((bit[4])(1 -_s 0xe)) == 0x3);
  test_assert("minus_range_vec_range_signed", ((int)(1 -_s 0xe)) == 3);*)
  (* returns (result, signed overflow, borrow in)*)
  test_assert ("minus_overflow_vec_signed0", (((bit[4], bit, bit))(0x1 -_s 0x1)) == (0x0, false, false));
  test_assert ("minus_overflow_vec_signed1", (((bit[4], bit, bit))(0x0 -_s 0x1)) == (0xf, true, true));
  test_assert ("minus_overflow_vec_signed2", (((bit[4], bit, bit))(0x8 -_s 0x1)) == (0x7, false, false));
  test_assert ("minus_overflow_vec_signed3", (((bit[4], bit, bit))(0x0 -_s 0x8)) == (0x8, true, true));

  test_assert ("minus_overflow_vec_bit_signed0", (((bit[4], bit, bit))(0x1 -_s bitone)) == (0x0, false, false));
  test_assert ("minus_overflow_vec_bit_signed1", (((bit[4], bit, bit))(0x0 -_s bitone)) == (0xf, true, true));
  test_assert ("minus_overflow_vec_bit_signed2", (((bit[4], bit, bit))(0x8 -_s bitone)) == (0x7, false, false));
  test_assert ("minus_overflow_vec_bit_signed3", (((bit[4], bit, bit))(0x8 -_s bitzero)) == (0x8, false, false));
}


function unit test_multiply () = {
  test_assert ("multiply", 6 * 9 == 54);
  test_assert ("multiply_vec", ((bit[8])(0x6 * 0xb)) == 0x42);
  test_assert ("mult_range_vec", ((bit[8])(6 * 0xb)) == 0x42);
  test_assert ("mult_vec_range", ((bit[8])(0x6 * 11)) == 0x42);
  (* XXX mult_oveflow_vec missing *)

  (* XXX not implmented
  test_assert ("multiply_signed", 6 *_s 9 == 54); *)
  test_assert ("multiply_vec_signed", ((bit[8])(0x6 *_s 0xb)) == 0xe2);
  test_assert ("mult_range_vec_signed", ((bit[8])(6 *_s 0xb)) == 0xe2);
  test_assert ("mult_vec_range_signed", ((bit[8])(0x6 *_s 11)) == 0xe2);

  (* XXX not sure what this should do...
  test_assert ("mult_overflow_vec_signed", ); *)
}

function unit test_div () = {
  test_assert ("divpospos_exact", (21 div 7) == 3);
  test_assert ("divposneg_exact", (21 div -7) == -3);
  test_assert ("divnegpos_exact", (-21 div 7) == -3);
  test_assert ("divnegneg_exact", (-21 div -7) == 3);

  test_assert ("divpospos_approx", (21 div 8) == 2);
  test_assert ("divposneg_approx", (21 div -8) == -2);
  test_assert ("divnegpos_approx", (-21 div 8) == -2);
  test_assert ("divnegneg_approx", (-21 div -8) == 2);

  (* XXX currently crashes on shallow embedding
  test_assert ("div_overflow", ((bit[8])(0x80 quot_s 0xff)) == 0x80);
  *)
}


function (bit[64]) run ((bit[64]) x) = {
  test_not();
  test_or();
  test_xor();
  test_and();
  test_leftshift();
  test_rightshift();
  test_rotate();
  test_duplicate();
  test_ext();
  test_add();
  test_add_signed();
  test_minus();
  test_minus_signed();
  test_multiply();
  test_div();
  return 0;
}

