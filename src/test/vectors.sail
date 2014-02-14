let (bit[32]) v = 0b101
let (bit[4]) v2 = [0,1,0,0]
register (bit[32]) i

register nat match_success

function unit decode ([bitzero, bitzero, bitone, bitzero]) = match_success := 1
and decode x = match_success := x

function bit main _ = {

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
  (* slice access of literal *)
  v[0];
}
