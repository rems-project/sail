
val cast forall Num 'n, Num 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [|0:2**'m - 1|] effect pure unsigned

val forall Num 'n, Num 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [|0 - (2**('m - 1)):2**('m - 1) - 1|] effect pure signed

val forall Num 'n, Num 'm. [|0:'n|] -> vector<'m - 1,'m,dec,bit> effect pure to_vec

val forall Num 'm. int -> vector<'m - 1,'m,dec,bit> effect pure to_svec

(* Vector access can't actually be properly polymorphic on vector
   direction because of the ranges being different for each type, so
   we overload it instead *)
val extern forall Num 'n, Num 'l, Type 'a, 'l >= 0. (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|]) -> 'a effect pure vector_access_dec
val extern forall Num 'n, Num 'l, Type 'a, 'l >= 0. (vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access_inc
val extern forall Num 'n, Num 'l, 'l >= 0. (vector<'n,'l,dec,bit>, [|'n - 'l + 1:'n|]) -> bit effect pure bitvector_access_dec
val extern forall Num 'n, Num 'l, 'l >= 0. (vector<'n,'l,inc,bit>, [|'n:'n + 'l - 1|]) -> bit effect pure bitvector_access_inc

overload vector_access [bitvector_access_inc; bitvector_access_dec; vector_access_inc; vector_access_dec]

(* Type safe vector subrange *)
(* vector_subrange(v, m, o) returns the subvector of v with elements with
   indices from m up to and *including* o. *)
val extern forall Num 'n, Num 'l, Num 'm, Num 'o, Type 'a, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,'a>, [:'m:], [:'o:]) -> vector<'m,('o - 'm) + 1,inc,'a> effect pure vector_subrange_inc

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, Type 'a, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  (vector<'n,'l,dec,'a>, [:'m:], [:'o:]) -> vector<'m,('m - 'o) + 1,dec,'a> effect pure vector_subrange_dec

val extern forall Num 'n, Num 'l.
  (vector<'n,'l,dec,bit>, int, int) -> list<bit> effect pure vector_subrange_bl_dec

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,bit>, [:'m:], [:'o:]) -> vector<'m,('o - 'm) + 1,inc,bit> effect pure bitvector_subrange_inc

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  (vector<'n,'l,dec,bit>, [:'m:], [:'o:]) -> vector<'m,('m - 'o) + 1,dec,bit> effect pure bitvector_subrange_dec

overload vector_subrange [bitvector_subrange_inc; bitvector_subrange_dec; vector_subrange_inc; vector_subrange_dec; vector_subrange_bl_dec]

(* Type safe vector append *)
val extern forall Num 'n1, Num 'l1, Num 'n2, Num 'l2, Order 'o, Type 'a, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,'a>, vector<'n2,'l2,'o,'a>) -> vector<'l1 + 'l2 - 1,'l1 + 'l2,'o,'a> effect pure vector_append = "vector_concat"

val extern forall Num 'n1, Num 'l1, Num 'n2, Num 'l2, Order 'o, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,bit>, vector<'n2,'l2,'o,bit>) -> vector<'l1 + 'l2 - 1,'l1 + 'l2,'o,bit> effect pure bitvector_append = "bitvector_concat"

val (list<bit>, list<bit>) -> list<bit> effect pure list_append

overload append [bitvector_append; vector_append; list_append]

(* Vector update *)

val extern forall Num 'n, Num 'l, Type 'a, 'l >= 0. (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|], 'a) -> vector<'n,'l,dec,'a> effect pure vector_update_dec
val extern forall Num 'n, Num 'l, Type 'a, 'l >= 0. (vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|], 'a) -> vector<'n,'l,dec,'a> effect pure vector_update_inc
val extern forall Num 'n, Num 'l, 'l >= 0. (vector<'n,'l,dec,bit>, [|'n - 'l + 1:'n|], bit) -> vector<'n,'l,dec,bit> effect pure bitvector_update_dec
val extern forall Num 'n, Num 'l, 'l >= 0. (vector<'n,'l,inc,bit>, [|'n:'n + 'l - 1|], bit) -> vector<'n,'l,dec,bit> effect pure bitvector_update_inc

overload vector_update [bitvector_update_dec; bitvector_update_inc; vector_update_dec; vector_update_inc]

(* Implicit register dereferencing *)
val cast forall Type 'a. register<'a> -> 'a effect {rreg} reg_deref

(* Bitvector duplication *)
val forall Num 'n. (bit, [:'n:]) -> vector<'n - 1,'n,dec,bit> effect pure duplicate

val (bit, int) -> list<bit> effect pure duplicate_to_list

val forall Num 'n, Num 'm, Num 'o, Order 'ord.
  (vector<'o,'n,'ord,bit>, [:'m:]) -> vector<'o,'m*'n,'ord,bit> effect pure duplicate_bits

val forall Num 'n, Num 'o, Order 'ord.
  (vector<'o,'n,'ord,bit>, int) -> list<bit> effect pure duplicate_bits_to_list

overload (deinfix ^^) [duplicate; duplicate_bits; duplicate_to_list; duplicate_bits_to_list]

(* Bitvector extension *)
val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure extz

val extern forall Num 'm, Num 'p, Order 'ord.
    list<bit> -> vector<'p, 'm, 'ord, bit> effect pure extz_bl

val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure exts

val extern forall Num 'm, Num 'p, Order 'ord.
    list<bit> -> vector<'p, 'm, 'ord, bit> effect pure exts_bl

(* If we want an automatic bitvector extension, then this is the function to
   use, but I've disabled the cast because it hides signedness bugs. *)
val extern (*cast*) forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord, 'm >= 'n.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure extzi

overload EXTZ [extz; extz_bl]
overload EXTS [exts; exts_bl]

val extern forall Type 'a, Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord, 'm >= 'o.
    vector<'n, 'm, 'ord, 'a> -> vector<'p, 'o, 'ord, 'a> effect pure mask

(* Adjust the start index of a decreasing bitvector *)
val cast forall Num 'n, Num 'm, 'n >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'m - 1,'m,dec,bit>
  effect pure norm_dec

val cast forall Num 'n, Num 'm, Num 'o, 'n >= 'm - 1, 'o >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'o,'m,dec,bit>
  effect pure adjust_dec

(* Various casts from 0 and 1 to bitvectors *)
val cast forall Num 'n, Num 'l. [:0:] -> vector<'n,'l,dec,bit> effect pure cast_0_vec_dec
val cast forall Num 'n, Num 'l. [:1:] -> vector<'n,'l,dec,bit> effect pure cast_1_vec_dec
val cast forall Num 'n, Num 'l. [|0:1|] -> vector<'n,'l,dec,bit> effect pure cast_01_vec_dec
val cast forall Num 'n, Num 'l. [:0:] -> vector<'n,'l,inc,bit> effect pure cast_0_vec_inc
val cast forall Num 'n, Num 'l. [:1:] -> vector<'n,'l,inc,bit> effect pure cast_1_vec_inc
val cast forall Num 'n, Num 'l. [|0:1|] -> vector<'n,'l,inc,bit> effect pure cast_01_vec_inc

val cast forall Num 'n, Order 'ord. vector<'n,1,'ord,bit> -> bool effect pure cast_vec_bool
val cast bit -> bool effect pure cast_bit_bool

val cast forall Num 'n, Num 'm, 'n >= 'm - 1, 'm >= 1. bit -> vector<'n,'m,dec,bit> effect pure cast_bit_vec

(* MSB *)
val forall Num 'n, Num 'm, Order 'ord. vector<'n, 'm, 'ord, bit> -> bit effect pure most_significant

(* Arithmetic *)

val extern forall Num 'n, Num 'm, Num 'o, Num 'p.
    ([|'n:'m|], [|'o:'p|]) -> [|'n + 'o:'m + 'p|] effect pure add_range = "add_int"

val extern (nat, nat) -> nat effect pure add_nat = "add_int"

val extern (int, int) -> int effect pure add_int

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure add_vec

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, int) -> vector<'o, 'n, 'ord, bit> effect pure add_vec_int

val forall Num 'n, Num 'o, Order 'ord.
    (int, vector<'o, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure add_int_vec

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> (vector<'o, 'n, 'ord, bit>, bit, bit) effect pure add_overflow_vec

val extern forall Num 'n, Num 'm, Num 'o, Num 'p.
    ([|'n:'m|], [|'o:'p|]) -> [|'n - 'p:'m - 'o|] effect pure sub_range = "sub_int"

val extern (int, int) -> int effect pure sub_int = "sub_int"

val forall Num 'n, Num 'm, Order 'ord.
    (vector<'n,'m,'ord,bit>, int) -> vector<'n,'m,'ord,bit> effect pure sub_vec_int

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure sub_vec

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> (vector<'o, 'n, 'ord, bit>, bit, bit) effect pure sub_underflow_vec

overload (deinfix +) [
  add_vec;
  add_overflow_vec;
  add_vec_int;
  add_int_vec;
  add_range;
  add_nat;
  add_int
]

overload (deinfix -) [
  sub_vec_int;
  sub_vec;
  sub_underflow_vec;
  sub_range;
  sub_int
]

val extern bool -> bit effect pure bool_to_bit = "bool_to_bitU"

val extern (int, int) -> int effect pure mult_int
val extern forall Num 'n, Num 'm. ([:'n:], [:'m:]) -> [:'n * 'm:] effect pure mult_range = "mult_int"
val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<2 * 'n - 1, 2 * 'n, 'ord, bit> effect pure mult_vec

overload (deinfix * ) [
  mult_vec;
  mult;
  mult_int
]

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<2 * 'n - 1, 2 * 'n, 'ord, bit> effect pure mult_svec

overload (deinfix *_s) [
  mult_svec
]

val extern (bool, bool) -> bool effect pure bool_xor

val extern forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure xor_vec = "bitwise_xor"

overload (deinfix ^) [
  bool_xor;
  xor_vec
]

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, int) -> vector<'o, 'n, 'ord, bit> effect pure shiftl

overload (deinfix <<) [
  shiftl
]

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, int) -> vector<'o, 'n, 'ord, bit> effect pure shiftr

overload (deinfix >>) [
  shiftr
]

(* Boolean operators *)
val extern bool -> bool effect pure bool_not = "not"
val (bool, bool) -> bool effect pure bool_or
val (bool, bool) -> bool effect pure bool_and

val forall Num 'n, Num 'm, Order 'ord.
    vector<'n,'m,'ord,bit> -> vector<'n,'m,'ord,bit> effect pure bitwise_not

val forall Num 'n, Num 'm, Order 'ord.
    (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> vector<'n,'m,'ord,bit> effect pure bitwise_and

val forall Num 'n, Num 'm, Order 'ord.
    (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> vector<'n,'m,'ord,bit> effect pure bitwise_or

overload ~ [bool_not; bitwise_not]
overload (deinfix &) [bool_and; bitwise_and]
overload (deinfix |) [bool_or; bitwise_or]

(* Equality *)

val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure eq_vec

val extern forall Type 'a. ('a, 'a) -> bool effect pure eq

val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure neq_vec

val extern forall Type 'a. ('a, 'a) -> bool effect pure neq

(*function forall Num 'n, Num 'm, Order 'ord. bool neq_vec (v1, v2) = bool_not(eq_vec(v1, v2))*)

overload (deinfix ==) [eq_vec; eq]
overload (deinfix !=) [neq_vec; neq]

val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure gteq_vec
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure gt_vec
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure lteq_vec
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure lt_vec

val extern (int, int) -> bool effect pure gteq_int = "gteq"
val extern (int, int) -> bool effect pure gt_int = "gt"
val extern (int, int) -> bool effect pure lteq_int = "lteq"
val extern (int, int) -> bool effect pure lt_int = "lt"

val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lt_range_atom = "lt"
val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lteq_range_atom = "lteq"
val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure gt_range_atom = "gt"
val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure gteq_range_atom = "gteq"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lt_atom_range = "lt"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lteq_atom_range = "lteq"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure gt_atom_range = "gt"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure gteq_atom_range = "gteq"

val extern forall Num 'n, Num 'm. ([:'n:], [:'m:]) -> bool effect pure lteq_atom_atom = "lteq"
val extern forall Num 'n, Num 'm. ([:'n:], [:'m:]) -> bool effect pure gteq_atom_atom = "gteq"
val extern forall Num 'n, Num 'm. ([:'n:], [:'m:]) -> bool effect pure lt_atom_atom = "lt"
val extern forall Num 'n, Num 'm. ([:'n:], [:'m:]) -> bool effect pure gt_atom_atom = "gt"

overload (deinfix >=) [gteq_atom_atom; gteq_range_atom; gteq_atom_range; gteq_vec; gteq_int]
overload (deinfix >) [gt_atom_atom; gt_range_atom; gt_vec; gt_int]
overload (deinfix <=) [lteq_atom_atom; lteq_range_atom; lteq_atom_range; lteq_vec; lteq_int]
overload (deinfix <) [lt_atom_atom; lt_range_atom; lt_vec; lt_int]

val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure gteq_svec
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure gt_svec
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure lteq_svec
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure lt_svec

overload (deinfix <_s) [lt_svec]
overload (deinfix <=_s) [lteq_svec]
overload (deinfix >_s) [gt_svec]
overload (deinfix >=_s) [gteq_svec]

val extern forall Num 'n, Num 'm, Num 'o, 'o >= 'n. ([|'n:'m|], [:'o:]) -> [|'n:'o|] effect pure min_range_atom = "min"
val extern (int, int) -> int effect pure min_int = "min"

overload min [min_range_atom; min_int]

val extern (int, int) -> int effect pure quotient = "quotient_int"

overload (deinfix quot) [quotient]

val extern (int, int) -> int effect pure modulo
val extern forall Num 'm. (int, [:'m:]) -> [|0:'m - 1|] effect pure modulo_atom = "modulo"

overload (deinfix mod) [modulo_atom; modulo]

val extern forall Num 'n. [:'n:] -> [:2** 'n:] effect pure pow2

val extern forall Num 'n, Num 'm, Order 'ord, Type 'a. vector<'n,'m,'ord,'a> -> [:'m:] effect pure vector_length = "length"
val extern forall Type 'a. list<'a> -> nat effect pure list_length

val extern forall Num 'n, Num 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [:'m:] effect pure bitvector_length = "bitvector_length"

overload length [bitvector_length; vector_length; list_length]

val cast forall Num 'n. [:'n:] -> [|'n|] effect pure upper

typedef option = const union forall Type 'a. {
    None;
    'a Some
}
