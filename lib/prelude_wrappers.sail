val extern forall Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,dec,bit> effect pure to_vec_dec
val extern forall Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,inc,bit> effect pure to_vec_inc
function forall Num 'n, Num 'm. (vector<'m - 1,'m,dec,bit>) to_vec (n) = to_vec_dec ((sizeof 'm) - 1, sizeof 'm, n)

function forall Num 'm. (vector<'m - 1,'m,dec,bit>) to_svec (n) = to_vec_dec ((sizeof 'm) - 1, sizeof 'm, n)

(* Bitvector extension *)
val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    ([:'p:], [:'m:], vector<'o, 'n, 'ord, bit>) -> vector<'p, 'm, 'ord, bit> effect pure extz' = "extz"
function forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    (vector<'p, 'm, 'ord, bit>) extz (v) = extz' (sizeof 'p, sizeof 'm, v)

val extern forall Num 'm, Num 'p, Order 'ord.
    ([:'p:], [:'m:], list<bit>) -> vector<'p, 'm, 'ord, bit> effect pure extz_bl' = "extz_bl"
function forall Num 'm, Num 'p, Order 'ord.
    (vector<'p, 'm, 'ord, bit>) extz_bl (v) = extz_bl' (sizeof 'p, sizeof 'm, v)

val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    ([:'p:], [:'m:], vector<'o, 'n, 'ord, bit>) -> vector<'p, 'm, 'ord, bit> effect pure exts' = "exts"
function forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    (vector<'p, 'm, 'ord, bit>) exts (v) = exts' (sizeof 'p, sizeof 'm, v)

val extern forall Num 'm, Num 'p, Order 'ord.
    ([:'p:], [:'m:], list<bit>) -> vector<'p, 'm, 'ord, bit> effect pure exts_bl' = "exts_bl"
function forall Num 'm, Num 'p, Order 'ord.
    vector<'p, 'm, 'ord, bit> exts_bl (v) = exts_bl' (sizeof 'p, sizeof 'm, v)

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

val extern forall Num 'n, Num 'm, 'n >= 'm - 1, 'm >= 1. ([:'n:], [:'m:], bit) -> vector<'n,'m,dec,bit> effect pure cast_bit_vec' = "cast_bit_vec"
function forall Num 'n, Num 'm, 'n >= 'm - 1, 'm >= 1. (vector<'n,'m,dec,bit>) cast_bit_vec b = cast_bit_vec' (sizeof 'n, sizeof 'm, b)
