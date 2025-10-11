
val foo : int -> (bool, bit, int, nat, bitvector(3))
function foo(n) = {
    (undefined_bool(), undefined_bit(), undefined_int(), undefined_nat(), undefined_bitvector(3))
}

val bar : int -> (vector(4, dec, int))
function bar(n) = {
    undefined_vector(4, n)
}
