default Order dec

$include <prelude.sail>

type x : Int = 8

type operator /('n : Int, 'm : Int) -> Int = div('n, 'm)

register r : bits(x / 2) = 0x0
