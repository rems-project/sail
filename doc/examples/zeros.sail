val zero_extend_1 : forall 'm 'n, 'm <= 'n. bits('m) -> bits('n)

val zero_extend_2 : forall 'm 'n, 'm <= 'n. (bits('m), int('n)) -> bits('n)

overload zero_extend = {zero_extend_1, zero_extend_2}