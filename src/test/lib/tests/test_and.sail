function unit test () = {
  test_assert ("bitwise_and", (0b0101 & 0b0011) == 0b0001);
  test_assert ("bitwise_and_00", (bitzero & bitzero) == bitzero);
  test_assert ("bitwise_and_01", (bitzero & bitone)  == bitzero);
  test_assert ("bitwise_and_10", (bitone  & bitzero) == bitzero);
  test_assert ("bitwise_and_11", (bitone  & bitone)  == bitone);
}
