type bit = Zero | One

val to_bool : bit -> bool
val bn : bit -> bit
val bor : bit -> bit -> bit
val xor : bit -> bit -> bit
val band : bit -> bit -> bit
val add : bit -> bit -> bit * bool
