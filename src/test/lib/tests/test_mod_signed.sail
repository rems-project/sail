function unit test () = {
  ();
  (* XXX mod_signed does exist on ocaml shallow embedding...
  test_assert ("mod_signed_pospos_exact", (21 mod_s 7) == 0);
  test_assert ("mod_signed_posneg_exact", (21 mod_s -7) == 0);
  test_assert ("mod_signed_negpos_exact", (-21 mod_s 7) == 0);
  test_assert ("mod_signed_negneg_exact", (-21 mod_s -7) == 0);

  test_assert ("mod_signed_pospos_approx", (21 mod_s 8) == 5);
  test_assert ("mod_signed_posneg_approx", (21 mod_s -8) == 5);
  test_assert ("mod_signed_negpos_approx", (-21 mod_s 8) == -5);
  test_assert ("mod_signed_negneg_approx", (-21 mod_s -8) == -5);
 
  (* XXX how to test this? Type checker should catch?
  test_assert ("mod_signed_zero", (21 mod_s 0) == undefined); *)

  test_assert("mod_vec_range_signed_pos", (0x7 mod_s 5) == 2);
  test_assert("mod_vec_range_signed_neg", (0xf mod_s 5) == -1);

  test_assert("mod_vec_signed_pos", (0x7 mod_s 0x5) == 0x2);
  test_assert("mod_vec_signed_neg", (0xf mod_s 0x5) == 0xf);
  test_assert("mod_vec_signed_pos_neg", (0x7 mod_s 0x8) == 0x7);
  test_assert("mod_vec_signed_neg_neg", (0xf mod_s 0x8) == 0x7);
  *)
}

