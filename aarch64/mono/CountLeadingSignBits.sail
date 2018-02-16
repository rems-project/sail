val CountLeadingSignBits : forall ('N : Int), 'N >= 3. bits('N) -> int

function CountLeadingSignBits x = return(CountLeadingZeroBits((x >> 1) ^ (x & slice_mask(0,'N))))
