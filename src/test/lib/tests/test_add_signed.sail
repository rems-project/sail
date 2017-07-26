function unit test() = {
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

