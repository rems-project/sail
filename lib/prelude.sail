
val cast forall Nat 'n, Nat 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [|0:2**'m - 1|] effect pure unsigned

(* Vector access can't actually be properly polymorphic on vector
   direction because of the ranges being different for each type, so
   we overload it instead *)
val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|]) -> 'a effect pure vector_access_dec
val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access_inc

(* Type safe vector subrange *)
val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,'a>, [:'m:], [:'o:]) -> vector<'m,'o - 'm,inc,'a> effect pure vector_subrange_inc

val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  (vector<'n,'l,dec,'a>, [:'m:], [:'o:]) -> vector<'m,('m - 'o) - 1,dec,'a> effect pure vector_subrange_dec

overload vector_subrange [vector_subrange_inc; vector_subrange_dec]

(* Type safe vector append *)
val forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, Type 'a, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,'a>, vector<'n2,'l2,'o,'a>) -> vector<'n1,'l1 + 'l2,'o,'a> effect pure vector_append

(* Implicit register dereferencing *)
val cast forall Type 'a. register<'a> -> 'a effect pure reg_deref

overload vector_access [vector_access_inc; vector_access_dec]

(* Bitvector duplication *)
val forall Nat 'n. (bit, [:'n:]) -> vector<'n - 1,'n,dec,bit> effect pure duplicate

val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord.
  (vector<'o,'n,'ord,bit>, [:'m:]) -> vector<'o,'m*'n,'ord,bit> effect pure duplicate_bits

overload (deinfix ^^) [duplicate; duplicate_bits]

(* Bitvector extension *)
val forall Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure extz

val forall Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure exts

overload EXTZ [extz]
overload EXTS [exts]

val forall Type 'a, Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord, 'm >= 'o.
    vector<'n, 'm, 'ord, 'a> -> vector<'p, 'o, 'ord, 'a> effect pure mask

(* Adjust the start index of a decreasing bitvector *)
val cast forall Nat 'n, Nat 'm, Nat 'o, 'n >= 'm - 1, 'o >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'o,'m,dec,bit>
  effect pure adjust_dec

(* Various casts from 0 and 1 to bitvectors *)
val cast forall Nat 'n, Nat 'l, Order 'ord. [:0:] -> vector<'n,'l,'ord,bit> effect pure cast_0_vec
val cast forall Nat 'n, Nat 'l, Order 'ord. [:1:] -> vector<'n,'l,'ord,bit> effect pure cast_1_vec
val cast forall Nat 'n, Nat 'l, Order 'ord. [|0:1|] -> vector<'n,'l,'ord,bit> effect pure cast_01_vec

val cast forall Nat 'n, Order 'ord. vector<'n,1,'ord,bit> -> bool effect pure cast_vec_bool
val cast bit -> bool effect pure cast_bit_bool

(* MSB *)
val forall Nat 'n, Nat 'm, Order 'ord. vector<'n, 'm, 'ord, bit> -> bit effect pure most_significant

(* Arithmetic *)

val forall Nat 'n, Nat 'm.
    (atom<'n>, atom<'m>) -> atom<'n+'m> effect pure add

val forall Nat 'n, Nat 'o, Nat 'p, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'p, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure add_vec

val forall Nat 'n, Nat 'o, Nat 'p, Nat 'q, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'p, 'n, 'ord, bit>) -> range<'q, 2**'n> effect pure add_vec_vec_range

(* FIXME: the parser is broken for 2**... it's just been hacked to work for this common case *)
val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (vector<'n, 'm, 'ord, bit>, atom<'o>) -> vector<'n, 'm, 'ord, bit> effect pure add_vec_range

val forall Nat 'n, Nat 'o, Nat 'p, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'p, 'n, 'ord, bit>) -> (vector<'o, 'n, 'ord, bit>, bit, bit) effect pure add_overflow_vec

(* but it doesn't parse this
val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (vector<'n, 'm, 'ord, bit>, atom<'o>) -> range<'o, 'o+2** 'm> effect pure add_vec_range_range
    *)

val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (atom<'o>, vector<'n, 'm, 'ord, bit>) -> vector<'n, 'm, 'ord, bit> effect pure add_range_vec

(* or this
val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (atom<'o>, vector<'n, 'm, 'ord, bit>) -> range<'o, 'o+2**'m-1> effect pure add_range_vec_range
*)

val forall Nat 'o, Nat 'p, Order 'ord.
    (vector<'o, 'p, 'ord, bit>, bit) -> vector<'o, 'p, 'ord, bit> effect pure add_vec_bit

val forall Nat 'o, Nat 'p, Order 'ord.
    (bit, vector<'o, 'p, 'ord, bit>) -> vector<'o, 'p, 'ord, bit> effect pure add_bit_vec

val forall Nat 'n, Nat 'm. ([:'n:], [:'m:]) -> [:'n - 'm:] effect pure sub_exact
val forall Nat 'n, Nat 'm, Nat 'o, 'o <= 'm - 'n. ([|'n:'m|], [:'o:]) -> [|'n:'m - 'o|] effect pure sub_range
val forall Nat 'n, Nat 'm, Order 'ord. (vector<'n,'m,'ord,bit>, int) -> vector<'n,'m,'ord,bit> effect pure sub_bv

overload (deinfix +) [
  add;
  add_vec;
  add_vec_vec_range;
  add_vec_range;
  add_overflow_vec;
  add_vec_range_range;
  add_range_vec;
  add_range_vec_range;
  add_vec_bit;
  add_bit_vec;
]

overload (deinfix -) [
  sub_exact;
  sub_bv;
  sub_range;
]

(* Equality *)

(* Sail gives a bunch of overloads for equality, but apparantly also
gives an equality and inequality for any type 'a, so why bother
overloading? *)

val forall Type 'a. ('a, 'a) -> bool effect pure eq
val forall Type 'a. ('a, 'a) -> bool effect pure neq

overload (deinfix ==) [eq]
overload (deinfix !=) [neq]

(* Boolean operators *)
val bool -> bool effect pure bool_not
val (bool, bool) -> bool effect pure bool_or
val (bool, bool) -> bool effect pure bool_and

overload ~ [bool_not]
overload (deinfix &) [bool_and]
overload (deinfix |) [bool_or]

(*
val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1. (vector<'n,'l,dec,'a>, [:'m:], [:'o:]) -> vector<'m,'m - 'o - 1,dec,'a> effect pure vector_subrange

val forall Nat 'n, Nat 'l, Order 'ord. ([|0:1|], vector<'n,'l,'ord,bit>) -> bool effect pure vec_eq_01_left
val forall Nat 'n, Nat 'l, Order 'ord. (vector<'n,'l,'ord,bit>, [|0:1|]) -> bool effect pure vec_eq_01_right

val forall Nat 'n, Nat 'l, Order 'ord. [|0:1|] -> vector<'n,'l,'ord,bit> effect pure cast_01_to_vec

val forall Nat 'n, Nat 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [|0:2**'m - 1|] effect pure cast_vec_to_range

val forall Type 'a. register<'a> -> 'a effect pure reg_deref

val forall Nat 'n, Nat 'l, Type 'a.
    (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|], 'a) -> vector<'n,'l,dec,'a>
    effect pure vector_update_dec

val forall Nat 'n, Nat 'm, Nat 'o, Type 'a, 'o <= 'm.
    vector<'n,'m,dec,'a> -> vector<'o - 1,'o,dec,'a>
    effect pure mask_dec

val forall Nat 'n, Nat 'm, Nat 'o, Type 'a, 'o <= 'm.
    vector<'n,'m,inc,'a> -> vector<0,'o,inc,'a>
    effect pure mask_inc

val bool -> bool effect pure not
val (bool, bool) -> bool effect pure bool_or
val (bool, bool) -> bool effect pure bool_and

val forall Nat 'n. vector<'n,'n,dec,bit> -> bool effect pure cast_dec_bv_to_bool

val bit -> bool effect pure cast_bit_to_bool

val forall Nat 'n, Nat 'm. ([:'n:], [:'m:]) -> [:'n - 'm:] effect pure sub_exact
val forall Nat 'n, Nat 'm, Nat 'o, 'o <= 'm - 'n. ([|'n:'m|], [:'o:]) -> [|'n:'m - 'o|] effect pure sub_range
val forall Nat 'n, Nat 'm, Order 'ord. (vector<'n,'m,'ord,bit>, int) -> vector<'n,'m,'ord,bit> effect pure sub_bv

val [:1:] -> bit effect pure cast_one_bit
val forall Nat 'n, Order 'ord. [:1:] -> vector<'n,1,'ord,bit> effect pure cast_one_bv
val [:0:] -> bit effect pure cast_zero_bit
val forall Nat 'n, Order 'ord. [:0:] -> vector<'n,1,'ord,bit> effect pure cast_zero_bv

val forall Type 'a. ('a, 'a) -> bool effect pure eq_anything
val forall Type 'a. ('a, 'a) -> bool effect pure neq_anything

val forall Nat 'n, Order 'ord. vector<'n,1,'ord,bit> -> bool effect pure cast_vec_bool

val forall Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord, 'm >= 'n.
  vector<'o,'n,'ord,bit> -> vector<'p,'m,'ord,bit> effect pure EXTS

val forall Nat 'n, Nat 'm, Order 'ord.
  (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> vector<'n,'m,'ord,bit>
  effect pure bv_add

val forall Nat 'n, Nat 'm, Nat 'o, 'n >= 'm - 1, 'o >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'o,'m,dec,bit>
  effect pure ADJUST
*)
