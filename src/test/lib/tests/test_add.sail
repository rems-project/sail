function unit test () = {
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

