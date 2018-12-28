type MyInt = {'n, true. atom('n)}

val add : forall 'n 'm. (atom('n), atom('m)) -> {'o, 'o == 'n + 'm. atom('o)}

val mult : forall 'n 'm. (atom('n), atom('m)) -> {'o, 'o == 'n * 'm. atom('o)}

overload operator + = {add}

overload operator * = {mult}

let x = 3 + 4

let y = x + x * x

let z : atom(7 * 8) = y

type Range('n: Int, 'm: Int), 'n <= 'm = {'o, 'n <= 'o & 'o <= 'm. atom('o)}

let a : Range(3, 4) = 3

let b : Range(2, 5) = a + 1
