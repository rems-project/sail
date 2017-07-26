function unit test () = {
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

