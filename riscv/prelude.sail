default Order dec

/* type bits ('n : Int) = vector('n - 1, 'n, dec, bit) */
type bits ('n : Int) = vector('n, dec, bit)
union option ('a : Type) = {None, Some : 'a}
infix 4 ==

val eq_atom = "eq_int" : forall 'n 'm. (atom('n), atom('m)) -> bool
val lteq_atom = "lteq" : forall 'n 'm. (atom('n), atom('m)) -> bool
val gteq_atom = "gteq" : forall 'n 'm. (atom('n), atom('m)) -> bool
val lt_atom = "lt" : forall 'n 'm. (atom('n), atom('m)) -> bool
val gt_atom = "gt" : forall 'n 'm. (atom('n), atom('m)) -> bool

val eq_int = "eq_int" : (int, int) -> bool

val eq_vec = "eq_list" : forall 'n. (bits('n), bits('n)) -> bool

val eq_string = "eq_string" : (string, string) -> bool

val eq_real = "eq_real" : (real, real) -> bool

val eq_anything = "(fun (x, y) -> x = y)" : forall ('a : Type). ('a, 'a) -> bool

val length = "length" : forall 'n ('a : Type). vector('n, dec, 'a) -> atom('n)

val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

overload operator == = {eq_atom, eq_int, eq_vec, eq_string, eq_real, eq_anything}

val vector_subrange = "subrange" : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val vector_access = "access" : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n.
  (vector('n, dec, 'a), atom('m)) -> 'a

val vector_update = "update" : forall 'n ('a : Type).
  (vector('n, dec, 'a), int, 'a) -> vector('n, dec, 'a)

val vector_update_subrange = "update_subrange" : forall 'n 'm 'o.
  (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

val vcons : forall ('n : Int) ('a : Type).
  ('a, vector('n, dec, 'a)) -> vector('n + 1, dec, 'a)

val append = "append" : forall ('n : Int) ('m : Int) ('a : Type).
  (vector('n, dec, 'a), vector('m, dec, 'a)) -> vector('n + 'm, dec, 'a)

val not_bool = "not" : bool -> bool

val not_vec = "not_vec" : forall 'n. bits('n) -> bits('n)

overload ~ = {not_bool, not_vec}

val neq_atom : forall 'n 'm. (atom('n), atom('m)) -> bool

function neq_atom (x, y) = not_bool(eq_atom(x, y))

val neq_int : (int, int) -> bool

function neq_int (x, y) = not_bool(eq_int(x, y))

val neq_vec : forall 'n. (bits('n), bits('n)) -> bool

function neq_vec (x, y) = not_bool(eq_vec(x, y))

val neq_anything : forall ('a : Type). ('a, 'a) -> bool

function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_atom, neq_int, neq_vec, neq_anything}

val and_bool = "and_bool" : (bool, bool) -> bool

val builtin_and_vec = "and_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val and_vec : forall 'n. (bits('n), bits('n)) -> bits('n)

function and_vec (xs, ys) = builtin_and_vec(xs, ys)

overload operator & = {and_bool, and_vec}

val or_bool = "or_bool" : (bool, bool) -> bool

val builtin_or_vec = "or_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val or_vec : forall 'n. (bits('n), bits('n)) -> bits('n)

function or_vec (xs, ys) = builtin_or_vec(xs, ys)

overload operator | = {or_bool, or_vec}

val unsigned = "uint" : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

val signed = "sint" : forall 'n. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

val hex_slice = "hex_slice" : forall 'n 'm. (string, atom('n), atom('m)) -> bits('n - 'm)

val __SetSlice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val __SetSlice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_SetSlice_int : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_GetSlice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n. (atom('n), int, int) -> bits('n)

function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val __raw_SetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int, bits('w)) -> bits('n)

val __raw_GetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int) -> bits('w)

val __ShiftLeft : forall 'm. (bits('m), int) -> bits('m)

val __SignExtendSlice : forall 'm. (bits('m), int, int) -> bits('m)

val __ZeroExtendSlice : forall 'm. (bits('m), int, int) -> bits('m)

val cast cast_unit_vec : bit -> bits(1)

val print = "prerr_endline" : string -> unit

val putchar = "putchar" : forall ('a : Type). 'a -> unit

val concat_str = "concat_str" : (string, string) -> string

val DecStr : int -> string

val HexStr : int -> string

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val xor_vec = "xor_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power : (int, int) -> int

val real_power = "real_power" : (real, int) -> real

overload operator ^ = {xor_vec, int_power, real_power}

val add_range = "add" : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_int = "add" : (int, int) -> int

val add_vec = "add_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_vec_int = "add_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val add_real = "add_real" : (real, real) -> real

overload operator + = {add_range, add_int, add_vec, add_vec_int, add_real}

val sub_range = "sub" : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val sub_int = "sub" : (int, int) -> int

val "sub_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val "sub_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val "sub_real" : (real, real) -> real

val negate_range = "minus_big_int" : forall 'n 'm. range('n, 'm) -> range(- 'm, - 'n)

val negate_int = "minus_big_int" : int -> int

val negate_real = "Num.minus_num" : real -> real

overload operator - = {sub_range, sub_int, sub_vec, sub_vec_int, sub_real}

overload negate = {negate_range, negate_int, negate_real}

val mult_range = "mult" : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n * 'o, 'm * 'p)

val mult_int = "mult" : (int, int) -> int

val mult_real = "mult_real" : (real, real) -> real

overload operator * = {mult_range, mult_int, mult_real}

val Sqrt = "sqrt_real" : real -> real

val gteq_int = "gteq" : (int, int) -> bool

val gteq_real = "gteq_real" : (real, real) -> bool

overload operator >= = {gteq_atom, gteq_int, gteq_real}

val lteq_int = "lteq" : (int, int) -> bool

val lteq_real = "lteq_real" : (real, real) -> bool

overload operator <= = {lteq_atom, lteq_int, lteq_real}

val gt_int = "gt" : (int, int) -> bool

val gt_real = "gt_real" : (real, real) -> bool

overload operator > = {gt_atom, gt_int, gt_real}

val lt_int = "lt" : (int, int) -> bool

val lt_real = "lt_real" : (real, real) -> bool

overload operator < = {lt_atom, lt_int, lt_real}

val RoundDown = "round_down" : real -> int

val RoundUp = "round_up" : real -> int

val abs_int = "abs_int" : int -> int

val abs_real = "abs_real" : real -> real

overload abs = {abs_int, abs_real}

val quotient_nat = "quotient" : (nat, nat) -> nat

val quotient_real = "quotient_real" : (real, real) -> real

val quotient = "quotient" : (int, int) -> int

infixl 7 /

overload operator / = {quotient_nat, quotient, quotient_real}

val modulus = "modulus" : (int, int) -> int

infixl 7 %

overload operator % = {modulus}

val Real = "Num.num_of_big_int" : int -> real

val shl_int = "shl_int" : (int, int) -> int

val shr_int = "shr_int" : (int, int) -> int

val min_nat = "min_int" : (nat, nat) -> nat

val min_int = "min_int" : (int, int) -> int

val max_nat = "max_int" : (nat, nat) -> nat

val max_int = "max_int" : (int, int) -> int

overload min = {min_nat, min_int}

overload max = {max_nat, max_int}

val __WriteRAM = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit

val __TraceMemoryWrite : forall 'n 'm.
  (atom('n), bits('m), bits(8 * 'n)) -> unit

val __ReadRAM = "read_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n)

val __TraceMemoryRead : forall 'n 'm. (atom('n), bits('m), bits(8 * 'n)) -> unit

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

val cast ex_nat : nat -> {'n, 'n >= 0. atom('n)}

function ex_nat 'n = n

val cast ex_int : int -> {'n, true. atom('n)}

function ex_int 'n = n

val cast ex_range : forall 'n 'm. range('n, 'm) -> {'o, 'n <= 'o <= 'm. atom('o)}

function ex_range (n as 'N) = n

val coerce_int_nat : int -> nat effect {escape}

function coerce_int_nat 'x = {
  assert(constraint('x >= 0));
  x
}

val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)

val pow2 = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)

val print_int = "print_int" : (string, int) -> unit

union exception = {
  Error_not_implemented : string,
  Error_misaligned_access,
}

val EXTS : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)
val EXTZ : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)

infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u

function operator <_s  (x : bits('n), y : bits('n)) -> forall 'n. bool = signed(x) < signed(y)
function operator >=_s (x : bits('n), y : bits('n)) -> forall 'n. bool = signed(x) >= signed(y)
function operator <_u  (x : bits('n), y : bits('n)) -> forall 'n. bool = unsigned(x) < unsigned(y)
function operator >=_u (x : bits('n), y : bits('n)) -> forall 'n. bool = unsigned(x) >= unsigned(y)

val cast bool_to_bits : bool -> bits(1)
function bool_to_bits x = if x then 0b1 else 0b0