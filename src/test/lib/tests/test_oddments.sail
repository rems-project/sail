function unit test () = {
  (* XXX this is weird, wrong type?
  test_assert("is_one0", not(is_one(bitzero)));
  test_assert("is_one1", is_one(bitone)); *)

  test_assert("signed-1", signed(0xf) == -1);
  test_assert("signed0",  signed(0x0) == 0);
  test_assert("signed1",  signed(0x1) == 1);

  test_assert("unsigned-1", unsigned(0xf) == 15);
  test_assert("unsigned0",  unsigned(0x0) == 0);
  test_assert("unsigned1",  unsigned(0x1) == 1);
}

