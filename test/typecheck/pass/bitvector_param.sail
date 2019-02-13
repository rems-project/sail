/* from prelude */
default Order dec
type bits ('n : Int) = vector('n, dec, bit)

val vector_subrange = {
  ocaml: "subrange",
  lem: "subrange_vec_dec",
  c: "vector_subrange",
  coq: "subrange_vec_dec"
} : forall ('n : Int) ('m : Int) ('o : Int), 0 <= 'o <= 'm < 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - 'o + 1)

val vector_update_subrange_dec = {ocaml: "update_subrange", c: "vector_update_subrange", lem: "update_subrange_vec_dec", coq: "update_subrange_vec_dec"} : forall 'n 'm 'o.
  (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

val vector_update_subrange_inc = {ocaml: "update_subrange", lem: "update_subrange_vec_inc"} : forall 'n 'm 'o.
  (vector('n, inc, bit), atom('m), atom('o), vector('o - ('m - 1), inc, bit)) -> vector('n, inc, bit)

overload vector_update_subrange = {vector_update_subrange_dec, vector_update_subrange_inc}

val bitvector_concat = {c: "append", ocaml: "append", lem: "concat_vec", coq: "concat_vec"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

val vector_concat = {ocaml: "append", lem: "append_list"} : forall ('n : Int) ('m : Int) ('a : Type).
  (vector('n, dec, 'a), vector('m, dec, 'a)) -> vector('n + 'm, dec, 'a)

overload append = {bitvector_concat, vector_concat}

val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}
/* sneaky deref with no effect necessary for bitfield writes */
val _reg_deref = "reg_deref" : forall ('a : Type). register('a) -> 'a

type xlen : Int = 64
type ylen : Int = 1

type xlenbits = bits(xlen)

bitfield Mstatus : xlenbits = {
  SD  : xlen - ylen,
  SXL : xlen - ylen - 1 .. xlen - ylen - 3
}
register mstatus : Mstatus
