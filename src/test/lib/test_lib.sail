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
  test_assert ("bitwise_not_bit0", ((~ (bitzero)) == bitone));
  test_assert ("bitwise_not_bit1", ((~ (bitone)) == bitzero));
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

  (* XXX don't think it's possible to set carryout out bit *)
  test_assert ("mult_overflow_vec_signed0", (((bit[8], bit, bit)) (0xf *_s 0x2)) == (0xfe, false, false));
  test_assert ("mult_overflow_vec_signed1", (((bit[8], bit, bit)) (0xf *_s 0xf)) == (0x01, false, false));
  test_assert ("mult_overflow_vec_signed2", (((bit[8], bit, bit)) (0x8 *_s 0x8)) == (0x40, true, false));
  test_assert ("mult_overflow_vec_signed3", (((bit[8], bit, bit)) (0x7 *_s 0x7)) == (0x31, true, false));
  test_assert ("mult_overflow_vec_signed4", (((bit[8], bit, bit)) (0x8 *_s 0x7)) == (0xc8, true, false));
}

function unit test_mod () = {
  test_assert ("modpospos_exact", (21 mod 7) == 0);
  test_assert ("modposneg_exact", (21 mod -7) == 0);
  test_assert ("modnegpos_exact", (-21 mod 7) == 0);
  test_assert ("modnegneg_exact", (-21 mod -7) == 0);

  test_assert ("modpospos_approx", (21 mod 8) == 5);
  test_assert ("modposneg_approx", (21 mod -8) == 5);
  test_assert ("modnegpos_approx", (-21 mod 8) == -5);
  test_assert ("modnegneg_approx", (-21 mod -8) == -5);
 
  (* XXX how to test this? Type checker should catch?
  test_assert ("mod_zero", (21 mod 0) == undefined); *)

  test_assert("mod_vec_range_pos", (0x7 mod 5) == 2);
  test_assert("mod_vec_range_neg", (0xf mod 5) == 0);

  test_assert("mod_vec_pos", (0x7 mod 0x5) == 0x2);
  test_assert("mod_vec_neg", (0xf mod 0x5) == 0x0);
  test_assert("mod_vec_pos_neg", (0x7 mod 0x8) == 0x7);
  test_assert("mod_vec_neg_neg", (0xf mod 0x8) == 0x7);
}

function unit test_mod_signed () = {
  ();
  (* XXX mod_signed does exist on ocaml shallow embedding...
  test_assert ("mod_signed_pospos_exact", (21 mod_s 7) == 0);
  test_assert ("mod_signed_posneg_exact", (21 mod_s -7) == 0);
  test_assert ("mod_signed_negpos_exact", (-21 mod_s 7) == 0);
  test_assert ("mod_signed_negneg_exact", (-21 mod_s -7) == 0);

  test_assert ("mod_signed_pospos_approx", (21 mod_s 8) == 5);
  test_assert ("mod_signed_posneg_approx", (21 mod_s -8) == 5);
  test_assert ("mod_signed_negpos_approx", (-21 mod_s 8) == -5);
  test_assert ("mod_signed_negneg_approx", (-21 mod_s -8) == -5);
 
  (* XXX how to test this? Type checker should catch?
  test_assert ("mod_signed_zero", (21 mod_s 0) == undefined); *)

  test_assert("mod_vec_range_signed_pos", (0x7 mod_s 5) == 2);
  test_assert("mod_vec_range_signed_neg", (0xf mod_s 5) == -1);

  test_assert("mod_vec_signed_pos", (0x7 mod_s 0x5) == 0x2);
  test_assert("mod_vec_signed_neg", (0xf mod_s 0x5) == 0xf);
  test_assert("mod_vec_signed_pos_neg", (0x7 mod_s 0x8) == 0x7);
  test_assert("mod_vec_signed_neg_neg", (0xf mod_s 0x8) == 0x7);
  *)
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

  (* quot and div are synonyms but let's check...  *)
  test_assert ("quotpospos_exact", (21 quot 7) == 3);
  test_assert ("quotposneg_exact", (21 quot -7) == -3);
  test_assert ("quotnegpos_exact", (-21 quot 7) == -3);
  test_assert ("quotnegneg_exact", (-21 quot -7) == 3);

  test_assert ("quotpospos_approx", (21 quot 8) == 2);
  test_assert ("quotposneg_approx", (21 quot -8) == -2);
  test_assert ("quotnegpos_approx", (-21 quot 8) == -2);
  test_assert ("quotnegneg_approx", (-21 quot -8) == 2);

  (* XXX currently crashes on shallow embedding
  test_assert ("div_overflow", ((bit[8])(0x80 quot_s 0xff)) == 0x80);
  *)
  test_assert ("quot_vec_pospos_exact", ((bit[8])(0x15 quot 0x07)) == 0x03);
  test_assert ("quot_vec_posneg_exact", ((bit[8])(0x15 quot 0xf9)) == 0x00);
  test_assert ("quot_vec_negpos_exact", ((bit[8])(0xeb quot 0x07)) == 0x21);
  test_assert ("quot_vec_negneg_exact", ((bit[8])(0xeb quot 0xf9)) == 0x00);

  test_assert ("quot_vec_pospos_approx", ((bit[8])(0x15 quot 0x08)) == 0x02);
  test_assert ("quot_vec_posneg_approx", ((bit[8])(0x15 quot 0xf8)) == 0x00);
  test_assert ("quot_vec_negpos_approx", ((bit[8])(0xeb quot 0x08)) == 0x1d);
  test_assert ("quot_vec_negneg_approx", ((bit[8])(0xeb quot 0xf8)) == 0x00);

  test_assert ("quot_overflow_vec", (((bit[8], bit, bit))(0x15 quot 0x08)) == (0x02, false, false));
  test_assert ("quot_overflow_vec", (((bit[8], bit, bit))(0x80 quot 0xff)) == (0x00, false, false));
}

function unit test_quot_signed () = {
  test_assert ("quot_vec_signed_pospos_exact", ((bit[8])(0x15 quot_s 0x07)) == 0x03);
  test_assert ("quot_vec_signed_posneg_exact", ((bit[8])(0x15 quot_s 0xf9)) == 0xfd);
  test_assert ("quot_vec_signed_negpos_exact", ((bit[8])(0xeb quot_s 0x07)) == 0xfd);
  test_assert ("quot_vec_signed_negneg_exact", ((bit[8])(0xeb quot_s 0xf9)) == 0x03);

  test_assert ("quot_vec_signed_pospos_approx", ((bit[8])(0x15 quot_s 0x08)) == 0x02);
  test_assert ("quot_vec_signed_posneg_approx", ((bit[8])(0x15 quot_s 0xf8)) == 0xfe);
  test_assert ("quot_vec_signed_negpos_approx", ((bit[8])(0xeb quot_s 0x08)) == 0xfe);
  test_assert ("quot_vec_signed_negneg_approx", ((bit[8])(0xeb quot_s 0xf8)) == 0x02);

  test_assert ("quot_signed_overflow_vec", (((bit[8], bit, bit))(0x15 quot_s 0x08)) == (0x02, false, false));
  (* XXX crashes shallow embedding due to undefined result
  let (result, overflow, carry) = ((bit[8], bit, bit))(0x80 quot_s 0xff) in {
    test_assert ("quot_signed_overflow_vec_ov", overflow);
    test_assert ("quot_signed_overflow_vec_ca", carry);
  };*)
}

function unit test_misc () = {
  test_assert ("power0", (0 ** 3) == 0);
  test_assert ("power1", (3 ** 0) == 1);
  test_assert ("power2", (11 ** 17) == 505447028499293771);
  (* XXX should be type error but isn't 
  test_assert ("power-1", (1 ** -1) == 0); *)

  test_assert ("abs_neg", (abs (-42)) == 42);
  test_assert ("abs_zero", (abs (0)) == 0);
  test_assert ("abs_pos", (abs (143)) == 143);

  test_assert ("max", max(-1, 1) == 1);
  test_assert ("min", min(-1, 1) == -1);

  test_assert ("length0", length([]) == 0);
  test_assert ("length1", length([bitzero]) == 1);
  test_assert ("length2", length(0x1234) == 16);
}

function unit test_eq () = {
  test_assert("eq_bit00", false == bitzero);
  test_assert("eq_bit01", not(false == bitone));
  test_assert("eq_bit10", not(true == bitzero));
  test_assert("eq_bit11", true == bitone);

  test_assert("eq_vec0", not (0x1 == 0x2));
  test_assert("eq_vec1", 0x2 == 0x2);
  test_assert("eq_vec_range0", not (0xf == 16));
  test_assert("eq_vec_range1", 0xf == 15);
  test_assert("eq_range_vec0", not (16 == 0xf));
  test_assert("eq_range_vec1", 15 == 0xf);
  test_assert("eq_range0", not(12 == 13));
  test_assert("eq_range1", 13 == 13);
  test_assert("eq_tup0", not ((true, false) == (bitzero, bitzero)));
  test_assert("eq_tup1", (true, false) == (bitone, bitzero));
}

function unit test_eq () = {
  test_assert("eq_bit00", false == bitzero);
  test_assert("eq_bit01", not(false == bitone));
  test_assert("eq_bit10", not(true == bitzero));
  test_assert("eq_bit11", true == bitone);

  test_assert("eq_vec0", not (0x1 == 0x2));
  test_assert("eq_vec1", 0x2 == 0x2);
  test_assert("eq_vec_range0", not (0xf == 16));
  test_assert("eq_vec_range1", 0xf == 15);
  test_assert("eq_range_vec0", not (16 == 0xf));
  test_assert("eq_range_vec1", 15 == 0xf);
  test_assert("eq_range0", not(12 == 13));
  test_assert("eq_range1", 13 == 13);
  test_assert("eq_tup0", not ((true, false) == (bitzero, bitzero)));
  test_assert("eq_tup1", (true, false) == (bitone, bitzero));
}

function unit test_neq () = {
  test_assert("neq_bit00", not(false != bitzero));
  test_assert("neq_bit01", false != bitone);
  test_assert("neq_bit10", true != bitzero);
  test_assert("neq_bit11", not(true != bitone));

  test_assert("neq_vec0", 0x1 != 0x2);
  test_assert("neq_vec1", not(0x2 != 0x2));
  test_assert("neq_vec_range0", 0xf != 16);
  test_assert("neq_vec_range0", 0x7 != 8);
  test_assert("neq_vec_range1", not(0xf != 15));
  (* XXX not implemented for ocaml
  test_assert("neq_range_vec0", 16 != 0xf);
  test_assert("neq_range_vec1", not(15 != 0xf)); *)
  test_assert("neq_range0", 12 != 13);
  test_assert("neq_range1", not(13 != 13));
  test_assert("neq_tup0", (true, false) != (bitzero, bitzero));
  test_assert("neq_tup1", not((true, false) != (bitone, bitzero)));
}

function unit test_lt() = {
  test_assert("lt0", not( 1 < -1));
  test_assert("lt1", not(-1 < -1));
  test_assert("lt2",    (-1 <  1));

  (* XXX default is signed -- document this! *)
  test_assert("lt_vec0", not(0x1 < 0xf));
  test_assert("lt_vec1", not(0xf < 0xf));
  test_assert("lt_vec2",    (0xf < 0x1));

  test_assert("lt_vec_range0", not(0x1 < -1));
  test_assert("lt_vec_range1", not(0xf < -1));
  test_assert("lt_vec_range2",    (0xf < 1));
  (* NB missing range_vec version *)

  (* XXX missing implementations
  test_assert("lt_unsigned0", not( 1 <_u -1));
  test_assert("lt_unsigned1", not(-1 <_u -1));
  test_assert("lt_unsigned2",    (-1 <_u  1)); *)

  test_assert("lt_vec_unsigned0",    (0x1 <_u 0xf));
  test_assert("lt_vec_unsigned1", not(0xf <_u 0xf));
  test_assert("lt_vec_unsigned2", not(0xf <_u 0x1));

  (* NB there is no lt_vec_range unsigned or signed *)

  (* XXX missing implementations 
  test_assert("lt_signed0", not( 1 <_s -1));
  test_assert("lt_signed1", not(-1 <_s -1));
  test_assert("lt_signed2",    (-1 <_s  1)); *)

  test_assert("lt_vec_signed0", not(0x1 <_s 0xf));
  test_assert("lt_vec_signed1", not(0xf <_s 0xf));
  test_assert("lt_vec_signed2",    (0xf <_s 0x1));
}

function unit test_gt() = {
  test_assert("gt0",    ( 1 > -1));
  test_assert("gt1", not(-1 > -1));
  test_assert("gt2", not(-1 >  1));

  (* XXX default is signed -- document this! *)
  test_assert("gt_vec0",    (0x1 > 0xf));
  test_assert("gt_vec1", not(0xf > 0xf));
  test_assert("gt_vec2", not(0xf > 0x1));

  test_assert("gt_vec_range0",    (0x1 > -1));
  test_assert("gt_vec_range1", not(0xf > -1));
  test_assert("gt_vec_range2", not(0xf > 1));
  (* NB missing range_vec version *)

  (* XXX missing implementations
  test_assert("gt_unsigned0",    ( 1 >_u -1));
  test_assert("gt_unsigned1", not(-1 >_u -1));
  test_assert("gt_unsigned2", not(-1 >_u  1)); *)

  test_assert("gt_vec_unsigned0", not(0x1 >_u 0xf));
  test_assert("gt_vec_unsigned1", not(0xf >_u 0xf));
  test_assert("gt_vec_unsigned2",    (0xf >_u 0x1));

  (* NB there is no gt_vec_range unsigned or signed *)

  (* XXX missing implementations 
  test_assert("gt_signed0",    ( 1 >_s -1));
  test_assert("gt_signed1", not(-1 >_s -1));
  test_assert("gt_signed2", not(-1 >_s  1)); *)

  test_assert("gt_vec_signed0",    (0x1 >_s 0xf));
  test_assert("gt_vec_signed1", not(0xf >_s 0xf));
  test_assert("gt_vec_signed2", not(0xf >_s 0x1));
}

function unit test_lteq() = {
  test_assert("lteq0", not( 1 <= -1));
  test_assert("lteq1",    (-1 <= -1));
  test_assert("lteq2",    (-1 <=  1));

  (* XXX default is signed -- document this! *)
  test_assert("lteq_vec0", not(0x1 <= 0xf));
  test_assert("lteq_vec1",    (0xf <= 0xf));
  test_assert("lteq_vec2",    (0xf <= 0x1));

  test_assert("lteq_vec_range0", not(0x1 <= -1));
  test_assert("lteq_vec_range1",    (0xf <= -1));
  test_assert("lteq_vec_range2",    (0xf <= 1));

  test_assert("lteq_range_vec0", not( 1 <= 0xf));
  test_assert("lteq_range_vec1",    (-1 <= 0xf));
  test_assert("lteq_range_vec2",    (-1 <= 0x1));

  (* XXX missing implementations
  test_assert("lteq_unsigned0", not( 1 <=_u -1));
  test_assert("lteq_unsigned1",    (-1 <=_u -1));
  test_assert("lteq_unsigned2",    (-1 <=_u  1)); *)

  (* XXX missing type / parser
  test_assert("lteq_unsigned_vec0",    (0x1 <=_u 0xf));
  test_assert("lteq_unsigned_vec1",    (0xf <=_u 0xf));
  test_assert("lteq_unsigned_vec2", not(0xf <=_u 0x1));*)

  (* NB there is no lteq_vec_range unsigned or signed *)

  (* XXX missing implementations 
  test_assert("lteq_signed0", not( 1 <=_s -1));
  test_assert("lteq_signed1",    (-1 <=_s -1));
  test_assert("lteq_signed2",    (-1 <=_s  1)); *)

  test_assert("lteq_vec_signed0", not(0x1 <=_s 0xf));
  test_assert("lteq_vec_signed1",    (0xf <=_s 0xf));
  test_assert("lteq_vec_signed2",    (0xf <=_s 0x1));
}

function unit test_gteq() = {
  test_assert("gteq0",    ( 1 >= -1));
  test_assert("gteq1",    (-1 >= -1));
  test_assert("gteq2", not(-1 >=  1));

  (* XXX default is signed -- document this! *)
  test_assert("gteq_vec0",    (0x1 >= 0xf));
  test_assert("gteq_vec1",    (0xf >= 0xf));
  test_assert("gteq_vec2", not(0xf >= 0x1));

  (* XXX odd type error here -- sail seems to prefer gteq_vec...
  test_assert("gteq_vec_range0",    (0x1 >= -1)); 
  test_assert("gteq_vec_range1",    (0xf >= -1));
  test_assert("gteq_vec_range2", not(0xf >= 1));

  test_assert("gteq_range_vec0",    ( 1 >= 0xf));
  test_assert("gteq_range_vec1",    (-1 >= 0xf));
  test_assert("gteq_range_vec2", not(-1 >= 0x1));*)

  (* XXX missing implementations
  test_assert("gteq_unsigned0",    ( 1 >=_u -1));
  test_assert("gteq_unsigned1", not(-1 >=_u -1));
  test_assert("gteq_unsigned2", not(-1 >=_u  1)); *)

  (* XXX missing
  test_assert("gteq_unsigned_vec0", not(0x1 >=_u 0xf));
  test_assert("gteq_unsigned_vec1", not(0xf >=_u 0xf));
  test_assert("gteq_unsigned_vec2",    (0xf >=_u 0x1)); *)

  (* NB there is no gteq_vec_range unsigned or signed *)

  (* XXX missing implementations 
  test_assert("gteq_signed0",    ( 1 >=_s -1));
  test_assert("gteq_signed1", not(-1 >=_s -1));
  test_assert("gteq_signed2", not(-1 >=_s  1)); *)

  test_assert("gteq_vec_signed0",    (0x1 >=_s 0xf));
  test_assert("gteq_vec_signed1",    (0xf >=_s 0xf));
  test_assert("gteq_vec_signed2", not(0xf >=_s 0x1));
}

function unit test_oddments () = {
  (* XXX this is weird, wrong type?
  test_assert("is_one0", not(is_one(bitzero)));
  test_assert("is_one1", is_one(bitone)); *)

  test_assert("signed-1", signed(0xf) == -1);
  test_assert("signed0",  signed(0x0) == 0);
  test_assert("signed1",  signed(0x1) == 1);

  test_assert("unsigned-1", unsigned(0xf) == 15);
  test_assert("unsigned0",  unsigned(0x0) == 0);
  test_assert("unsigned1",  unsigned(0x1) == 1);
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
  test_mod();
  test_mod_signed();
  test_div();
  test_quot_signed();
  test_misc();
  test_eq();
  test_neq();
  test_lt();
  test_gt();
  test_lteq();
  test_gteq();
  test_oddments();
  return 0;
}

