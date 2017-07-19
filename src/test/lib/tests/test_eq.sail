function unit test () = {
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

