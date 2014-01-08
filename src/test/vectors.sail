let (bit[32]) v = 0b101
register (bit[32]) i

function unit main _ = {

  i := [bitzero, bitzero, bitone, bitzero];
  i := 0b101 ;
  i[0] := bitzero;
  (* XXX Vector access of non-vector *)
  v[0];
}
