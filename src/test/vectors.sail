let (bit[32]) v = 0b101
register (bit[32]) i

register nat match_success

function unit decode ([bitzero, bitzero, bitone, bitzero]) = match_success := 1
and decode x = match_success := x

function unit main _ = {

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

  (* XXX function clause match fail *)
  (* parameter is wrapped in a 1-tuple upon call, but probably not
  unwrapped for the pattern-matching *)
  decode(i);

  (* concatenation *)
  switch i {
    (* XXX match fails *)
    case ([bitzero] : [bitzero, bitone] : [bitzero]) -> match_success := 1
    (* but this works *)
    case ([bitzero] : [bitzero] : [bitone] : [bitzero]) -> match_success := 2
    case _ -> match_success := i
  };

  (* XXX slice access not implemented *)
  i[0] := bitzero;
  (* XXX Vector access of non-vector *)
  v[0];
}
