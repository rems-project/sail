

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
  (*
  XXX something in here causes sail to infinite loop
  test_assert ("bitwise_xor_00", (bitzero ^ bitzero) == bitzero);
  test_assert ("bitwise_xor_01", (bitzero ^ bitone)  == bitone);
  test_assert ("bitwise_xor_10", (bitone  ^ bitzero) == bitone);
  test_assert ("bitwise_xor_11", (bitone  ^ bitone)  == bitzero);*)

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

  return 0;
}

