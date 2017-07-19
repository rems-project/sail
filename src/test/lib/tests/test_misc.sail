function unit test () = {
  test_assert ("power0", (0 ** 3) == 0);
  test_assert ("power1", (3 ** 0) == 1);
  test_assert ("power2", (11 ** 17) == 505447028499293771);
  (* XXX should be type error but isn't 
  test_assert ("power-1", (1 ** -1) == 0); *)

  test_assert ("abs_neg", (abs (-42)) == 42);
  test_assert ("abs_zero", (abs (0)) == 0);
  test_assert ("abs_pos", (abs (143)) == 143);

  test_assert ("max", max(-1, 1) == 1);
  test_assert ("min", min(-1, 1) == -1);

  test_assert ("length0", length([]) == 0);
  test_assert ("length1", length([bitzero]) == 1);
  test_assert ("length2", length(0x1234) == 16);
}

