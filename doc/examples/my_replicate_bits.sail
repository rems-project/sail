default Order dec

$include <prelude.sail>

infixl 7 <<
infixl 7 >>

val operator << = pure "shiftl" : forall 'm. (bits('m), int) -> bits('m)
val shiftl = pure "shiftl" : forall 'm. (bits('m), int) -> bits('m)

val operator >> = pure {
  ocaml: "shiftr_ocaml",
  c: "shiftr_c",
  lem: "shiftr_lem",
  _: "shiftr"
} : forall 'm. (bits('m), int) -> bits('m)

val zero_extend = pure "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

overload operator | = {or_vec}

val my_replicate_bits : forall 'n 'm, 'm >= 1 & 'n >= 1.
    (int('n), bits('m)) -> bits('n * 'm)

val zeros = pure "zeros" : forall 'n. atom('n) -> bits('n)

function my_replicate_bits(n, xs) = {
    var ys = zeros(n * length(xs));
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

val extz : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function extz(m, xs) = zero_extend(xs, m)

function extz_usage() -> unit = {
    let xs: bits(32) = 0x0000_0000;
    let ys: bits(64) = extz(xs);
}
