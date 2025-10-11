default Order dec

$include <prelude.sail>

function unif_bitvec_append(x: bitvector(13), y: bitvector(3)) -> bitvector(4*4) = {
    bitvector_concat(x, y)
}

function unif_bitvec_replicate(x: bitvector(4)) -> bitvector(2*8) = {
    replicate_bits(x, 4)
}

function unif_subrange_bits(x: bitvector(16)) -> bitvector(17 - 10 + 1) = {
    subrange_bits(x, 10, 3)
}

val unif_vector_subrange : forall 'n, 'n >= 0. (int('n), bitvector(8 * 'n + 8)) -> bitvector(8)
function unif_vector_subrange(i, v) = {
    vector_subrange(v, 8 * i + 7, 8 * i)
}
