

scattered typedef ast = const union
val ast -> unit effect pure execute
scattered function unit execute

union ast member (unit) DUMMY
function clause execute (DUMMY) = ()

end ast
end execute

(*val extern string -> unit effect {wmv} printt*)

function unit test_assert (name, pred) = {
  print (name);
  if pred then
    print (": pass\n")
  else
    print(": fail\n")
}

function (bit[64]) run ((bit[64]) x) = {
  test_assert ("not_bit0", (not (bitzero)) == bitone);
  test_assert ("not_bit1", (not (bitone)) == bitzero);

  test_assert ("bitwise_not", (~ (0b01) == 0b10));
  test_assert ("bitwise_not_bit0", (~ (bitzero) == bitone));
  test_assert ("bitwise_not_bit1", (~ (bitone) == bitzero));

  test_assert ("bitwise_or", (0b0101 | 0b0011) == 0b0111);
  test_assert ("bitwise_or_00", (bitzero | bitzero) == bitzero);
  test_assert ("bitwise_or_01", (bitzero | bitone)  == bitone);
  test_assert ("bitwise_or_10", (bitone  | bitzero) == bitone);
  test_assert ("bitwise_or_11", (bitone  | bitone)  == bitone);

  test_assert ("bitwise_xor", (0b0101 ^ 0b0011) == 0b0110);
  test_assert ("bitwise_xor_00", (bitzero ^ bitzero) == bitzero);
  test_assert ("bitwise_xor_01", (bitzero ^ bitone)  == bitone);
  test_assert ("bitwise_xor_10", (bitone  ^ bitzero) == bitone);
  test_assert ("bitwise_xor_11", (bitone  ^ bitone)  == bitzero);

  test_assert ("bitwise_and", (0b0101 & 0b0011) == 0b0001);
  test_assert ("bitwise_and_00", (bitzero & bitzero) == bitzero);
  test_assert ("bitwise_and_01", (bitzero & bitone)  == bitzero);
  test_assert ("bitwise_and_10", (bitone  & bitzero) == bitzero);
  test_assert ("bitwise_and_11", (bitone  & bitone)  == bitone);
  
  test_assert ("divpospos_exact", (21 div 7) == 3);
  test_assert ("divposneg_exact", (21 div -7) == -3);
  test_assert ("divnegpos_exact", (-21 div 7) == -3);
  test_assert ("divnegneg_exact", (-21 div -7) == 3);

  test_assert ("divpospos_approx", (21 div 8) == 2);
  test_assert ("divposneg_approx", (21 div -8) == -2);
  test_assert ("divnegpos_approx", (-21 div 8) == -2);
  test_assert ("divnegneg_approx", (-21 div -8) == 2);

  (* XXX currently crashes on shallow embedding
  test_assert ("div_overflow", ((bit[8])(0x80 quot_s 0xff)) == 0x80);
  *)

  test_assert ("leftshift_small0", (0x99 << 0) == 0x99);
  test_assert ("leftshift_small3", (0x99 << 3) == 0xc8);
  test_assert ("leftshift_small7", (0x99 << 7) == 0x80);
  test_assert ("leftshift_small8", (0x99 << 8) == 0x00);
  test_assert ("leftshift_big0", (0x99999999999999999 << 0) == 0x99999999999999999);
  test_assert ("leftshift_big3", (0x99999999999999999 << 3) == 0xcccccccccccccccc8);
  test_assert ("leftshift_big7", (0x99999999999999999 << 7) == 0xccccccccccccccc80);
  test_assert ("leftshift_big68", (0x99999999999999999 << 68) == 0x00000000000000000);

  test_assert ("rightshift_small0", (0x99 >> 0) == 0x99);
  test_assert ("rightshift_small3", (0x99 >> 3) == 0x13);
  test_assert ("rightshift_small7", (0x99 >> 7) == 0x01);
  test_assert ("rightshift_small8", (0x99 >> 8) == 0x00); (* XXX fails on interp *)
  test_assert ("rightshift_big0", (0x99999999999999999 >> 0) == 0x99999999999999999);
  test_assert ("rightshift_big3", (0x99999999999999999 >> 3) == 0x13333333333333333);
  test_assert ("rightshift_big7", (0x99999999999999999 >> 7) == 0x01333333333333333);
  test_assert ("rightshift_big68", (0x99999999999999999 >> 68) == 0x00000000000000000); (* XXX fails on interp *)

  test_assert ("rotate0", (0x99 <<< 0) == 0x99); (* XXX fails on interp *)
  test_assert ("rotate3", (0x99 <<< 3) == 0xcc);
  test_assert ("rotate7", (0x99 <<< 7) == 0xcc);
  test_assert ("rotate8", (0x99 <<< 8) == 0x99);

  (* XXX crashes on shallow embedding
  test_assert ("duplicate_empty", (bitzero ^^ 0) == []); *)
  test_assert ("duplicate0", (bitzero ^^ 8) == 0x00);
  test_assert ("duplicate1", (bitone ^^ 8) == 0xff);

  (* XXX crashes on shallow embedding 
  test_assert ("duplicate_bits0", (0x21 ^^ 0) == []);*)
  test_assert ("duplicate_bits1", (0xce ^^ 1) == 0xce);
  test_assert ("duplicate_bits9", (0xce ^^ 9) == 0xcecececececececece);
  test_assert ("duplicate_covfefe", (0xc0 : (0xfe ^^ 2)) == 0xc0fefe);

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

  return 0;
}

