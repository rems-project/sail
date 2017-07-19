function unit test () = {
  test_assert ("extz0", EXTZ(0b00) == 0x00);
  test_assert ("extz1", EXTZ(0b10) == 0x02);
  test_assert ("extz2", EXTZ(0b10) == 0b10);
  test_assert ("extz3", EXTZ(0b10) == 0b0);
  
  test_assert ("exts0", EXTS(0b00) == 0x00);
  test_assert ("exts1", EXTS(0b10) == 0xfe);
  test_assert ("exts2", EXTS(0b10) == 0b10);
  test_assert ("exts3", EXTS(0b10) == 0b0);

  test_assert ("most_significant0", most_significant(0b011) == bitzero);
  test_assert ("most_significant1", most_significant(0b100) == bitone);
  }

