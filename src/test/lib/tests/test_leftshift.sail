function unit test () = {
  test_assert ("leftshift_small0", (0x99 << 0) == 0x99);
  test_assert ("leftshift_small3", (0x99 << 3) == 0xc8);
  test_assert ("leftshift_small7", (0x99 << 7) == 0x80);
  test_assert ("leftshift_small8", (0x99 << 8) == 0x00);
  test_assert ("leftshift_big0", (0x99999999999999999 << 0) == 0x99999999999999999);
  test_assert ("leftshift_big3", (0x99999999999999999 << 3) == 0xcccccccccccccccc8);
  test_assert ("leftshift_big7", (0x99999999999999999 << 7) == 0xccccccccccccccc80);
  test_assert ("leftshift_big68", (0x99999999999999999 << 68) == 0x00000000000000000);
}

