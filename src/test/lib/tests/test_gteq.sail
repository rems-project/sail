function unit test() = {
  test_assert("gteq0",    ( 1 >= -1));
  test_assert("gteq1",    (-1 >= -1));
  test_assert("gteq2", not(-1 >=  1));

  (* XXX default is signed -- document this! *)
  test_assert("gteq_vec0",    (0x1 >= 0xf));
  test_assert("gteq_vec1",    (0xf >= 0xf));
  test_assert("gteq_vec2", not(0xf >= 0x1));

  (* XXX odd type error here -- sail seems to prefer gteq_vec...
  test_assert("gteq_vec_range0",    (0x1 >= -1)); 
  test_assert("gteq_vec_range1",    (0xf >= -1));
  test_assert("gteq_vec_range2", not(0xf >= 1));

  test_assert("gteq_range_vec0",    ( 1 >= 0xf));
  test_assert("gteq_range_vec1",    (-1 >= 0xf));
  test_assert("gteq_range_vec2", not(-1 >= 0x1));*)

  (* XXX missing implementations
  test_assert("gteq_unsigned0",    ( 1 >=_u -1));
  test_assert("gteq_unsigned1", not(-1 >=_u -1));
  test_assert("gteq_unsigned2", not(-1 >=_u  1)); *)

  (* XXX missing
  test_assert("gteq_unsigned_vec0", not(0x1 >=_u 0xf));
  test_assert("gteq_unsigned_vec1", not(0xf >=_u 0xf));
  test_assert("gteq_unsigned_vec2",    (0xf >=_u 0x1)); *)

  (* NB there is no gteq_vec_range unsigned or signed *)

  (* XXX missing implementations 
  test_assert("gteq_signed0",    ( 1 >=_s -1));
  test_assert("gteq_signed1", not(-1 >=_s -1));
  test_assert("gteq_signed2", not(-1 >=_s  1)); *)

  test_assert("gteq_vec_signed0",    (0x1 >=_s 0xf));
  test_assert("gteq_vec_signed1",    (0xf >=_s 0xf));
  test_assert("gteq_vec_signed2", not(0xf >=_s 0x1));
}

