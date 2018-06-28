val BigEndianReverse = {lem: "BigEndianReverse"} : forall ('width : Int), 'width >= 0 & 'width >= 0.
  bits('width) -> bits('width) effect {escape}

function BigEndianReverse value_name = {
  assert(('width == 8) | (('width == 16) | (('width == 32) | (('width == 64) | ('width == 128)))));
  result : bits('width) = replicate_bits(0b0,'width);
  foreach (i from 0 to ('width - 1) by 8)
    result[i+7 .. i] = (value_name['width-i - 1 .. 'width-i - 8] : bits(8));
  return result
}
