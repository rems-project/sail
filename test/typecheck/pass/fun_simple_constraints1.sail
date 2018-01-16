val plus : forall ('n : Int) ('m : Int).
  (atom('n + 20), atom('m)) -> atom('n + 20 + 'm)

val minus_ten_id : forall ('n : Int), 'n <= -10. atom('n) -> atom('n)

val ten_id : forall ('n : Int), 'n >= 10. atom('n) -> atom('n)

val branch : forall ('N : Int), 'N >= 63. range(10, 'N) -> range(10, 'N)

function branch x = x
and branch y : range(10, 30) = y
and branch _ : atom(31) = 'N
and branch _ : range(31, 40) = plus(60, 3)
and branch _ : range(41, 50) = plus('N, minus_ten_id(-53))
and branch _ : range(51, 63) = ten_id('N)
