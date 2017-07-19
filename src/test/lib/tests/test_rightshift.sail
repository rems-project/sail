function unit test () = {
  test_assert ("rightshift_small0", (0x99 >> 0) == 0x99);
  test_assert ("rightshift_small3", (0x99 >> 3) == 0x13);
  test_assert ("rightshift_small7", (0x99 >> 7) == 0x01);
  test_assert ("rightshift_small8", (0x99 >> 8) == 0x00); (* XXX fails on interp *)
  test_assert ("rightshift_big0", (0x99999999999999999 >> 0) == 0x99999999999999999);
  test_assert ("rightshift_big3", (0x99999999999999999 >> 3) == 0x13333333333333333);
  test_assert ("rightshift_big7", (0x99999999999999999 >> 7) == 0x01333333333333333);
  test_assert ("rightshift_big68", (0x99999999999999999 >> 68) == 0x00000000000000000); (* XXX fails on interp *)
}
