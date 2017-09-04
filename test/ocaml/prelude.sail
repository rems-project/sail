
default Order dec

val extern (int, int) -> bool effect pure eq_int = "eq_int"
val extern forall 'n. (bit['n], bit['n]) -> bool effect pure eq_vec = "eq_list"
val extern (string, string) -> bool effect pure eq_string = "eq_string"
val (real, real) -> bool effect pure eq_real

val extern forall Type 'a. ('a, 'a) -> bool effect pure eq_anything = "(fun (x, y) -> x == y)"

overload (deinfix ==) [eq_int; eq_vec; eq_string; eq_real; eq_anything]

val extern forall Type 'a, Num 'n. vector<'n - 1, 'n, dec, 'a> -> [:'n:] effect pure length = "length"

val extern forall Num 'n, Num 'm, Num 'o (* , 'm >= 'o, 'o >= 0, 'n >= 'm + 1 *).
  (bit['n], [:'m:], [:'o:]) -> bit['m - ('o - 1)] effect pure vector_subrange = "subrange"

val extern forall Num 'n, Type 'a. (vector<'n - 1, 'n, dec, 'a>, int) -> 'a effect pure vector_access = "access"

val extern forall Num 'n, Type 'a. (vector<'n - 1, 'n, dec, 'a>, int, 'a) -> vector<'n - 1, 'n, dec, 'a> effect pure vector_update = "update"

val extern forall Num 'n, Num 'm, Num 'o.
  (bit['n], [:'m:], [:'o:], bit['m - ('o - 1)]) -> bit['n]
  effect pure vector_update_subrange = "update_subrange"

val forall Num 'n, Type 'a. ('a, vector<'n - 1, 'n, dec, 'a>) -> vector<'n, 'n + 1, dec, 'a> effect pure vcons

val extern forall Num 'n, Num 'm, Type 'a. (vector<'n - 1, 'n, dec, 'a>, vector<'m - 1, 'm, dec, 'a>) -> vector<('n + 'm) - 1, 'n + 'm, dec, 'a> effect pure append = "append"

val extern bool -> bool effect pure not_bool = "not"
val extern forall 'n. bit['n] -> bit['n] effect pure not_vec = "not_vec"

overload ~ [not_bool; not_vec]

val forall Type 'a. ('a, 'a) -> bool effect pure neq_anything

function neq_anything (x, y) = not_bool (x == y)

overload (deinfix !=) [neq_anything]

val extern (bool, bool) -> bool effect pure and_bool = "and_bool"
val extern forall 'n. (bit['n], bit['n]) -> bit['n] effect pure and_vec = "and_vec"

overload (deinfix &) [and_bool; and_vec]

val extern (bool, bool) -> bool effect pure or_bool = "or_bool"
val extern forall 'n. (bit['n], bit['n]) -> bit['n] effect pure or_vec = "or_vec"

overload (deinfix |) [or_bool; or_vec]

val extern forall 'n. bit['n] -> [|0:2**'n - 1|] effect pure UInt = "uint"

val extern forall 'n. bit['n] -> [|- 2**('n - 1):2**('n - 1) - 1|] effect pure SInt = "sint"

val extern string -> unit effect pure print = "print_endline"
val extern (string, string) -> string effect pure concat_str = "concat_string"
val int -> string effect pure DecStr
val int -> string effect pure HexStr

val forall 'n. (bit['n], bit['n]) -> bit['n] effect pure xor_vec
val (int, int) -> int effect pure int_exp

overload (deinfix ^) [xor_vec; int_exp]

val extern forall 'n, 'm, 'o, 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n+'o:'m+'p|] effect pure add_range = "add"
val extern (int, int) -> int effect pure add_int = "add"
val extern forall 'n. (bit['n], bit['n]) -> bit['n] effect pure add_vec = "add_vec"
val forall 'n. (bit['n], int) -> bit['n] effect pure add_vec_int

overload (deinfix +) [add_range; add_int; add_vec; add_vec_int]

val extern forall 'n, 'm, 'o, 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n-'p:'m-'o|] effect pure sub_range = "sub"
val extern (int, int) -> int effect pure sub_int = "sub"
val forall 'n. (bit['n], bit['n]) -> bit['n] effect pure sub_vec
val forall 'n. (bit['n], int) -> bit ['n] effect pure sub_vec_int

val forall 'n. [|'n:'m|] -> [|-'m:-'n|] effect pure negate_range
val int -> int effect pure negate_int

overload (deinfix -) [sub_range; sub_int; sub_vec; sub_vec_int]
overload negate [negate_range; negate_int]

val extern forall 'n, 'm, 'o, 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n * 'o : 'm * 'p|] effect pure mult_range = "mult"
val extern (int, int) -> int effect pure mult_int = "mult"

overload (deinfix * ) [mult_range; mult_int]

val (int, int) -> bool effect pure gteq_int
val (real, real) -> bool effect pure gteq_real

overload (deinfix >=) [gteq_int; gteq_real]

val (int, int) -> bool effect pure lteq_int
val (real, real) -> bool effect pure lteq_real

overload (deinfix <=) [lteq_int; lteq_real]

val (int, int) -> bool effect pure gt_int
val (real, real) -> bool effect pure gt_real

overload (deinfix >) [gt_int; gt_real]

val (int, int) -> bool effect pure lt_int
val (real, real) -> bool effect pure lt_real

overload (deinfix <) [lt_int; lt_real]

val real -> int effect pure RoundDown
val real -> int effect pure RoundUp

val extern (int, int) -> int effect pure quotient = "quotient"

overload (deinfix quot) [quotient]

val extern (int, int) -> int effect pure modulus = "modulus"

overload (deinfix mod) [modulus]

val extern (int, int) -> int effect pure shl_int
val extern (int, int) -> int effect pure shr_int

val (nat, nat) -> nat effect pure min_nat
val (int, int) -> int effect pure min_int
val (nat, nat) -> nat effect pure max_nat
val (int, int) -> int effect pure max_int

overload min [min_nat; min_int]
overload max [max_nat; max_int]

val extern forall 'n, 'm. ([:'m:], [:'n:], bit['m], bit['m], bit[8 * 'n]) -> unit effect {wmem} __WriteRAM = "write_ram"
val extern forall 'n, 'm. ([:'m:], [:'n:], bit['m], bit['m]) -> bit[8 * 'n] effect {rmem} __ReadRAM = "read_ram"

val extern forall 'n, 'm. (bit['n], [:'m:]) -> bit['n * 'm] effect pure replicate_bits

val extern nat -> exist 'n, 'n >= 0. [:'n:] effect pure ex_nat = "identity"
val extern int -> exist 'n. [:'n:] effect pure ex_int = "identity"
val extern forall 'n, 'm. [|'n:'m|] -> exist 'o, 'n <= 'o & 'o <= 'm. [:'o:] effect pure ex_range = "identity"

