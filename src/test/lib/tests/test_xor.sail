function unit test () = {
  test_assert ("bitwise_xor", (0b0101 ^ 0b0011) == 0b0110);
  test_assert ("bitwise_xor_00", (bitzero ^ bitzero) == bitzero);
  test_assert ("bitwise_xor_01", (bitzero ^ bitone)  == bitone);
  test_assert ("bitwise_xor_10", (bitone  ^ bitzero) == bitone);
  test_assert ("bitwise_xor_11", (bitone  ^ bitone)  == bitzero);
}
