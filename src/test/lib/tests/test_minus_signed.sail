function unit test() = {
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

