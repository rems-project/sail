function unit test () = {
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

