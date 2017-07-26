function unit test () = {
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
