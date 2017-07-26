function unit test() = {
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

