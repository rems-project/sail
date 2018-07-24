default Order dec

$include <prelude.sail>

infixl 7 <<
infixl 7 >>

val operator << = "shiftl" : forall 'm. (bits('m), int) -> bits('m)
val "shiftl" : forall 'm. (bits('m), int) -> bits('m)

val operator >> = {
  ocaml: "shiftr_ocaml",
  c: "shiftr_c",
  lem: "shiftr_lem",
  _: "shiftr"
} : forall 'm. (bits('m), int) -> bits('m)

val "or_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val zero_extend = "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

overload operator | = {or_vec}

val my_replicate_bits : forall 'n 'm, 'm >= 1 & 'n >= 1. (int('n), bits('m)) -> bits('n * 'm)

val zeros = "zeros" : forall 'n. atom('n) -> bits('n)

function my_replicate_bits(n, xs) = {
  ys = zeros(n * length(xs));
  foreach (i from 1 to n) {
    ys = ys << length(xs);
    ys = ys | zero_extend(xs, length(ys))
  };
  ys
}

val my_replicate_bits_2 : forall 'n 'm, 'm >= 1 & 'n >= 1. (int('n), bits('m)) -> bits('n * 'm)

function my_replicate_bits_2(n, xs) = {
  ys = zeros('n * 'm);
  foreach (i from 1 to n) {
    ys = (ys << 'm) | zero_extend(xs, 'n * 'm)
  };
  ys
}

val cast extz : forall 'n 'm, 'm >= 'n. bits('n) -> bits('m)

function extz(xs) = zero_extend(xs, 'm)

val my_replicate_bits_3 : forall 'n 'm, 'm >= 1 & 'n >= 1. (int('n), bits('m)) -> bits('n * 'm)

function my_replicate_bits_3(n, xs) = {
  ys = zeros('n * 'm);
  foreach (i from 1 to n) ys = ys << 'm | xs;
  ys
}