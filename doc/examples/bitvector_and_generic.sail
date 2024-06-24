default Order dec

$include <vector.sail>

function same_order() -> unit = {
    let a_generic_vector : vector(3, bit) = [bitzero, bitzero, bitone];
    let a_bitvector : bits(3) = [bitzero, bitzero, bitone]; // 0b001

    assert(a_generic_vector[0] == bitone);
    assert(a_bitvector[0] == bitone)
}
