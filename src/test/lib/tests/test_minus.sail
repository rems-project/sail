function unit test() = {
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

