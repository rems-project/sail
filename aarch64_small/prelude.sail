default Order dec

union option ('a : Type) = {None : unit, Some : 'a}

type bits ('n : Int) = vector('n, dec, bit)

infix 7 >>
infix 7 <<

val operator >> = "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)
val operator << = "shift_bits_left" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)


infix 7 ^^

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
val operator ^^ = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)


infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u
infix 4 <=_u

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator <=_u : forall 'n. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)
function operator <=_u (x, y) = unsigned(x) <= unsigned(y)