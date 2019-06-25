val CountLeadingSignBits : forall 'N, 'N >= 2. bits('N) -> int

function CountLeadingSignBits x = return(CountLeadingZeroBits((sail_shiftright(x, 1)) ^ (x & slice_mask(0,'N))))
