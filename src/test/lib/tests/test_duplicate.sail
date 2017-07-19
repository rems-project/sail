function unit test () = {
  (* XXX crashes on shallow embedding
  should type have a constraint n>0?
  test_assert ("duplicate_empty", (bitzero ^^ 0) == []); *)
  test_assert ("duplicate0", (bitzero ^^ 8) == 0x00);
  test_assert ("duplicate1", (bitone ^^ 8) == 0xff);

  (* XXX crashes on shallow embedding 
  test_assert ("duplicate_bits0", (0x21 ^^ 0) == []);*)
  test_assert ("duplicate_bits1", (0xce ^^ 1) == 0xce);
  test_assert ("duplicate_bits9", (0xce ^^ 9) == 0xcecececececececece);
  test_assert ("duplicate_covfefe", (0xc0 : (0xfe ^^ 2)) == 0xc0fefe);
}

