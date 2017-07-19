function unit test () = { 
  test_assert ("rotate0", (0x99 <<< 0) == 0x99); (* XXX fails on interp *)
  test_assert ("rotate3", (0x99 <<< 3) == 0xcc);
  test_assert ("rotate7", (0x99 <<< 7) == 0xcc);
  test_assert ("rotate8", (0x99 <<< 8) == 0x99);
}

