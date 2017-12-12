val extern forall Num 'l, Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,dec,bit> effect pure to_vec_dec
val extern forall Num 'l, Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,inc,bit> effect pure to_vec_inc
function forall Num 'n, Num 'm. (vector<'m - 1,'m,dec,bit>) to_vec (n) = to_vec_dec ((sizeof 'm) - 1, sizeof 'm, n)

function forall Num 'm. (vector<'m - 1,'m,dec,bit>) to_svec (n) = to_vec_dec ((sizeof 'm) - 1, sizeof 'm, n)

(* Vector access *)

val extern forall Num 'n, Num 'l, Type 'a, 'l >= 0. ([:'n:], vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|]) -> 'a effect pure vector_access_dec' = "vector_access_dec"
function forall Num 'n, Num 'l, Type 'a, 'l >= 0. 'a vector_access_dec ((vector<'n,'l,dec,'a>) v, i) = vector_access_dec' (sizeof 'n, v, i)
val extern forall Num 'n, Num 'l, Type 'a, 'l >= 0. ([:'n:], vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access_inc' = "vector_access_inc"
function forall Num 'n, Num 'l, Type 'a, 'l >= 0. 'a vector_access_inc ((vector<'n,'l,inc,'a>) v, i) = vector_access_inc' (sizeof 'n, v, i)
val extern forall Num 'n, Num 'l, 'l >= 0. ([:'n:], vector<'n,'l,dec,bit>, [|'n - 'l + 1:'n|]) -> bit effect pure bitvector_access_dec' = "bitvector_access_dec"
function forall Num 'n, Num 'l, 'l >= 0. bit bitvector_access_dec ((vector<'n,'l,dec,bit>) v, i) = bitvector_access_dec' (sizeof 'n, v, i)
val extern forall Num 'n, Num 'l, 'l >= 0. ([:'n:], vector<'n,'l,inc,bit>, [|'n:'n + 'l - 1|]) -> bit effect pure bitvector_access_inc' = "bitvector_access_inc"
function forall Num 'n, Num 'l, 'l >= 0. bit bitvector_access_inc ((vector<'n,'l,inc,bit>) v, i) = bitvector_access_inc' (sizeof 'n, v, i)
function forall Num 'n, 'n >= 0. bit bitvector_access_dec_norm ((vector<'n - 1,'n,dec,bit>) v, i) = bitvector_access_dec' (sizeof 'n - 1, v, i)
function forall Num 'n, 'n >= 0. bit bitvector_access_inc_norm ((vector<0,'n,inc,bit>) v, i) = bitvector_access_inc' (0, v, i)
function forall Num 'n, Type 'a, 'n >= 0. 'a vector_access_dec_norm ((vector<'n - 1,'n,dec,'a>) v, i) = vector_access_dec' (sizeof 'n - 1, v, i)
function forall Num 'n, Type 'a, 'n >= 0. 'a vector_access_inc_norm ((vector<0,'n,inc,'a>) v, i) = vector_access_inc' (0, v, i)

(* Vector subrange *)

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, Type 'a, 'l >= 0, 'm <= 'o, 'o <= 'l.
  ([:'n:], vector<'n,'l,inc,'a>, [:'m:], [:'o:]) -> vector<'m,('o - 'm) + 1,inc,'a> effect pure vector_subrange_inc' = "vector_subrange_inc"
function vector_subrange_inc (v, i, j) = vector_subrange_inc' (sizeof 'n, v, i, j)

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, Type 'a, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  ([:'n:], vector<'n,'l,dec,'a>, [:'m:], [:'o:]) -> vector<'m,('m - 'o) + 1,dec,'a> effect pure vector_subrange_dec' = "vector_subrange_dec"
function vector_subrange_dec (v, i, j) = vector_subrange_dec' (sizeof 'n, v, i, j)

val extern forall Num 'n, Num 'l.
  ([:'n:], vector<'n,'l,dec,bit>, int, int) -> list<bit> effect pure vector_subrange_bl_dec' = "vector_subrange_bl_dec"
function vector_subrange_bl_dec (v, i, j) = vector_subrange_bl_dec' (sizeof 'n, v, i, j)

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, 'l >= 0, 'm <= 'o, 'o <= 'l.
  ([:'n:], vector<'n,'l,inc,bit>, [:'m:], [:'o:]) -> vector<'m,('o - 'm) + 1,inc,bit> effect pure bitvector_subrange_inc' = "bitvector_subrange_inc"
function bitvector_subrange_inc (v, i, j) = bitvector_subrange_inc' (sizeof 'n, v, i, j)

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  ([:'n:], vector<'n,'l,dec,bit>, [:'m:], [:'o:]) -> vector<'m,('m - 'o) + 1,dec,bit> effect pure bitvector_subrange_dec' = "bitvector_subrange_dec"
function bitvector_subrange_dec (v, i, j) = bitvector_subrange_dec' (sizeof 'n, v, i, j)

(* Vector subrange update *)

val extern forall Num 'n, Num 'l, Num 'i, Num 'j, Num 'o, Type 'a, 'l >= 0. ([:'n:], vector<'n,'l,dec,'a>, [:'i:], [:'j:], vector<'o,'i - 'j + 1,dec,'a>) -> vector<'n,'l,dec,'a> effect pure vector_update_subrange_dec' = "vector_update_subrange_dec"
val extern forall Num 'n, Num 'l, Num 'i, Num 'j, Num 'o, Type 'a, 'l >= 0. ([:'n:], vector<'n,'l,inc,'a>, [:'i:], [:'j:], vector<'o,'j - 'i + 1,inc,'a>) -> vector<'n,'l,inc,'a> effect pure vector_update_subrange_inc' = "vector_update_subrange_inc"
val extern forall Num 'n, Num 'l, Num 'i, Num 'j, Num 'o, 'l >= 0. ([:'n:], vector<'n,'l,dec,bit>, [:'i:], [:'j:], vector<'o,'i - 'j + 1,dec,bit>) -> vector<'n,'l,dec,bit> effect pure bitvector_update_subrange_dec' = "bitvector_update_subrange_dec"
val extern forall Num 'n, Num 'l, Num 'i, Num 'j, Num 'o, 'l >= 0. ([:'n:], vector<'n,'l,inc,bit>, [:'i:], [:'j:], vector<'o,'j - 'i + 1,inc,bit>) -> vector<'n,'l,dec,bit> effect pure bitvector_update_subrange_inc' = "bitvector_update_subrange_inc"

function vector_update_subrange_dec (v, i, j, v') = vector_update_subrange_dec' (sizeof 'n, v, i, j, v')
function vector_update_subrange_inc (v, i, j, v') = vector_update_subrange_inc' (sizeof 'n, v, i, j, v')
function bitvector_update_subrange_dec (v, i, j, v') = bitvector_update_subrange_dec' (sizeof 'n, v, i, j, v')
function bitvector_update_subrange_inc (v, i, j, v') = bitvector_update_subrange_inc' (sizeof 'n, v, i, j, v')

(* Bitvector extension *)
val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    ([:'p:], [:'m:], vector<'o, 'n, 'ord, bit>) -> vector<'p, 'm, 'ord, bit> effect pure extz' = "extz"
function forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    (vector<'p, 'm, 'ord, bit>) extz (v) = extz' (sizeof 'p, sizeof 'm, v)

val extern forall Num 'm, Num 'p, Order 'ord.
    ([:'p:], [:'m:], list<bit>) -> vector<'p, 'm, 'ord, bit> effect pure cast_bl_vec = "cast_bl_vec"
function forall Num 'm, Num 'p, Order 'ord.
    (vector<'p, 'm, 'ord, bit>) extz_bl (v) = cast_bl_vec (sizeof 'p, sizeof 'm, v)

val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    ([:'p:], [:'m:], vector<'o, 'n, 'ord, bit>) -> vector<'p, 'm, 'ord, bit> effect pure exts' = "exts"
function forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    (vector<'p, 'm, 'ord, bit>) exts (v) = exts' (sizeof 'p, sizeof 'm, v)

val extern forall Num 'm, Num 'p, Order 'ord.
    ([:'p:], [:'m:], list<bit>) -> vector<'p, 'm, 'ord, bit> effect pure cast_bl_svec = "cast_bl_svec"
function forall Num 'm, Num 'p, Order 'ord.
    vector<'p, 'm, 'ord, bit> exts_bl (v) = cast_bl_svec (sizeof 'p, sizeof 'm, v)

val extern forall Type 'a, Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord, 'm >= 'o.
    ([:'p:], [:'o:], vector<'n, 'm, 'ord, 'a>) -> vector<'p, 'o, 'ord, 'a> effect pure mask' = "extz"
function forall Type 'a, Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord, 'm >= 'o.
    (vector<'p, 'o, 'ord, 'a>) mask (v) = mask' (sizeof 'p, sizeof 'o, v)

(* Adjust the start index of a decreasing bitvector *)
val extern forall Num 'n, Num 'm, Num 'o, 'n >= 'm - 1, 'o >= 'm - 1.
  ([:'o:], vector<'n,'m,dec,bit>) -> vector<'o,'m,dec,bit>
  effect pure adjust_dec' = "adjust_start_index"
function forall Num 'n, Num 'm, Num 'o, 'n >= 'm - 1, 'o >= 'm - 1.
  (vector<'o,'m,dec,bit>) adjust_dec (v) = adjust_dec' (sizeof 'o, v)

(* Various casts from 0 and 1 to bitvectors *)
function forall Num 'n, Num 'l. (vector<'n,'l,dec,bit>) cast_0_vec_dec i = to_vec_dec (sizeof 'n, sizeof 'l, i)
function forall Num 'n, Num 'l. (vector<'n,'l,dec,bit>) cast_1_vec_dec i = to_vec_dec (sizeof 'n, sizeof 'l, i)
function forall Num 'n, Num 'l. (vector<'n,'l,dec,bit>) cast_01_vec_dec i = to_vec_dec (sizeof 'n, sizeof 'l, i)
function forall Num 'n, Num 'l. (vector<'n,'l,inc,bit>) cast_0_vec_inc i = to_vec_inc (sizeof 'n, sizeof 'l, i)
function forall Num 'n, Num 'l. (vector<'n,'l,inc,bit>) cast_1_vec_inc i = to_vec_inc (sizeof 'n, sizeof 'l, i)
function forall Num 'n, Num 'l. (vector<'n,'l,inc,bit>) cast_01_vec_inc i = to_vec_inc (sizeof 'n, sizeof 'l, i)

val extern forall Num 'n, Num 'm, 'n >= 'm - 1, 'm >= 1. ([:'n:], [:'m:], bit) -> vector<'n,'m,dec,bit> effect pure cast_bit_vec' = "cast_bit_vec_basic"
function forall Num 'n, Num 'm, 'n >= 'm - 1, 'm >= 1. (vector<'n,'m,dec,bit>) cast_bit_vec b = cast_bit_vec' (sizeof 'n, sizeof 'm, b)
