$ifndef __REAL
$define __REAL

val "neg_real" : real -> real

val "mult_real" : (real, real) -> real

overload operator * = {mult_real}

val "sub_real" : (real, real) -> real

overload operator - = {sub_real}

val "add_real" : (real, real) -> real

overload operator + = {add_real}

val "div_real" : (real, real) -> real

overload operator / = {div_real}

val sqrt = "sqrt_real" : real -> real

val "abs_real" : real -> real

val floor = "round_down" : real -> int

val ceil = "round_up" : real -> int

val "to_real" : int -> real

val "eq_real" : (real, real) -> bool
val "lt_real" : (real, real) -> bool
val "gt_real" : (real, real) -> bool
val "lteq_real" : (real, real) -> bool
val "gteq_real" : (real, real) -> bool

overload operator == = {eq_real}
overload operator < = {lt_real}
overload operator > = {gt_real}
overload operator <= = {lteq_real}
overload operator >= = {gteq_real}

val pow_real = "real_power" : (real, int) -> real

val "print_real" : (string, real) -> unit
val "prerr_real" : (string, real) -> unit

val "random_real" : unit -> real

$endif
