function unit test() = {
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

