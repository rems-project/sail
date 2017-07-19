function unit test () = {
  test_assert ("bitwise_or", (0b0101 | 0b0011) == 0b0111);
  test_assert ("bitwise_or_00", (bitzero | bitzero) == bitzero);
  test_assert ("bitwise_or_01", (bitzero | bitone)  == bitone);
  test_assert ("bitwise_or_10", (bitone  | bitzero) == bitone);
  test_assert ("bitwise_or_11", (bitone  | bitone)  == bitone);
}
