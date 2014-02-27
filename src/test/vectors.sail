let (bit[32]) v = 0b101
let (bit[4]) v2 = [0,1,0,0]
register (bit[32]) i

let (bit[10]) v3 = 0b0101010111
register (bit[5]) slice_check

register nat match_success

function unit decode ([bitzero, bitzero, bitone, bitzero]) = match_success := 1
and decode x = match_success := x

function bit main _ = {

  slice_check := v3;
  slice_check := v3[1..10];
  slice_check := v3[5..10];

  i := [bitzero, bitzero, bitone, bitzero];

  (* literal match *)
  switch v {
    case 0b101 -> match_success := 1
    case _ -> match_success := v
  };

  switch i {
    case [bitzero, bitzero, bitone, bitzero] -> match_success := 1
    case _ -> match_success := i
  };

  decode(i);

  (* concatenation *)
  switch i {
    case ([bitzero] : [bitzero, bitone] : [bitzero]) -> match_success := 1
    case _ -> match_success := i
  };
  switch i {
    (* check order of concatenation *)
    case ([bitzero] : [bitone] : [bitzero] : [bitzero]) -> match_success := 99
    case ([bitzero] : [bitzero] : [bitone] : [bitzero]) -> match_success := 1
    case _ -> match_success := i
  };

  (* indexed match *)
  switch i {
    case [0=bitzero, 1=bitzero, 2=bitone, 3=bitzero] -> match_success := 1
    case _ -> match_success := i
  };

  (* slice update *)
  i[0] := bitzero;
  i[2 .. 3] := [bitone, bitone];

  (* slice access of literal *)
  v[0];
}
