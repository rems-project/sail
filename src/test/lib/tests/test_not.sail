function unit test () = {
  test_assert ("not_bit0", (not (bitzero)) == bitone);
  test_assert ("not_bit1", (not (bitone)) == bitzero);

  test_assert ("bitwise_not", (~ (0b01) == 0b10));
  test_assert ("bitwise_not_bit0", ((~ (bitzero)) == bitone));
  test_assert ("bitwise_not_bit1", ((~ (bitone)) == bitzero));
}
