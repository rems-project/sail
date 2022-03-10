$include <arith.sail>

val pow2 = pure "pow2" : forall 'n, 'n >= 0. int('n) -> int(2 ^ 'n)

val floor_pow2 : forall ('x : Int), 'x >= 0. int('x) -> int

function floor_pow2 x = {
    if x == 0 then {
        return(0);
    } else {
        n : {'n, 'n >= 1. int('n)} = 1;
        while x >= pow2(n) do {
            n = n + 1
        };
        return(pow2(n - 1))
    }
}
