val BigEndianReverse : forall 'W, 'W in {8,16,32,64,128}. bits('W) -> bits('W) effect pure

function BigEndianReverse value_name = {
  result : bits('W) = replicate_bits(0b0,'W);
  foreach (i from 0 to ('W - 8) by 8)
    result[i+7 .. i] = (value_name['W-i - 1 .. 'W-i - 8] : bits(8));
  return result
}
