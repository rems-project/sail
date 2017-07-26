function unit test () = {
  test_assert ("modpospos_exact", (21 mod 7) == 0);
  test_assert ("modposneg_exact", (21 mod -7) == 0);
  test_assert ("modnegpos_exact", (-21 mod 7) == 0);
  test_assert ("modnegneg_exact", (-21 mod -7) == 0);

  test_assert ("modpospos_approx", (21 mod 8) == 5);
  test_assert ("modposneg_approx", (21 mod -8) == 5);
  test_assert ("modnegpos_approx", (-21 mod 8) == -5);
  test_assert ("modnegneg_approx", (-21 mod -8) == -5);
 
  (* XXX how to test this? Type checker should catch?
  test_assert ("mod_zero", (21 mod 0) == undefined); *)

  test_assert("mod_vec_range_pos", (0x7 mod 5) == 2);
  test_assert("mod_vec_range_neg", (0xf mod 5) == 0);

  test_assert("mod_vec_pos", (0x7 mod 0x5) == 0x2);
  test_assert("mod_vec_neg", (0xf mod 0x5) == 0x0);
  test_assert("mod_vec_pos_neg", (0x7 mod 0x8) == 0x7);
  test_assert("mod_vec_neg_neg", (0xf mod 0x8) == 0x7);
}

