function unit test () = {
  test_assert("neq_bit00", not(false != bitzero));
  test_assert("neq_bit01", false != bitone);
  test_assert("neq_bit10", true != bitzero);
  test_assert("neq_bit11", not(true != bitone));

  test_assert("neq_vec0", 0x1 != 0x2);
  test_assert("neq_vec1", not(0x2 != 0x2));
  test_assert("neq_vec_range0", 0xf != 16);
  test_assert("neq_vec_range0", 0x7 != 8);
  test_assert("neq_vec_range1", not(0xf != 15));
  (* XXX not implemented for ocaml
  test_assert("neq_range_vec0", 16 != 0xf);
  test_assert("neq_range_vec1", not(15 != 0xf)); *)
  test_assert("neq_range0", 12 != 13);
  test_assert("neq_range1", not(13 != 13));
  test_assert("neq_tup0", (true, false) != (bitzero, bitzero));
  test_assert("neq_tup1", not((true, false) != (bitone, bitzero)));
}

