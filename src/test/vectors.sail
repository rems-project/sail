let (bit[32]) v = 0b101
register (bit[32]) i

function unit main _ = {

  i := [bitzero, bitzero, bitone, bitzero];
  i := 0b101 ;
  (* unbound identifier *)
  i[0] := bitzero;
  (* unbound identifier *)
  v[0];


}
