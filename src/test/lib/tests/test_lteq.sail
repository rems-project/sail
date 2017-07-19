function unit test() = {
  test_assert("lteq0", not( 1 <= -1));
  test_assert("lteq1",    (-1 <= -1));
  test_assert("lteq2",    (-1 <=  1));

  (* XXX default is signed -- document this! *)
  test_assert("lteq_vec0", not(0x1 <= 0xf));
  test_assert("lteq_vec1",    (0xf <= 0xf));
  test_assert("lteq_vec2",    (0xf <= 0x1));

  test_assert("lteq_vec_range0", not(0x1 <= -1));
  test_assert("lteq_vec_range1",    (0xf <= -1));
  test_assert("lteq_vec_range2",    (0xf <= 1));

  test_assert("lteq_range_vec0", not( 1 <= 0xf));
  test_assert("lteq_range_vec1",    (-1 <= 0xf));
  test_assert("lteq_range_vec2",    (-1 <= 0x1));

  (* XXX missing implementations
  test_assert("lteq_unsigned0", not( 1 <=_u -1));
  test_assert("lteq_unsigned1",    (-1 <=_u -1));
  test_assert("lteq_unsigned2",    (-1 <=_u  1)); *)

  (* XXX missing type / parser
  test_assert("lteq_unsigned_vec0",    (0x1 <=_u 0xf));
  test_assert("lteq_unsigned_vec1",    (0xf <=_u 0xf));
  test_assert("lteq_unsigned_vec2", not(0xf <=_u 0x1));*)

  (* NB there is no lteq_vec_range unsigned or signed *)

  (* XXX missing implementations 
  test_assert("lteq_signed0", not( 1 <=_s -1));
  test_assert("lteq_signed1",    (-1 <=_s -1));
  test_assert("lteq_signed2",    (-1 <=_s  1)); *)

  test_assert("lteq_vec_signed0", not(0x1 <=_s 0xf));
  test_assert("lteq_vec_signed1",    (0xf <=_s 0xf));
  test_assert("lteq_vec_signed2",    (0xf <=_s 0x1));
}

