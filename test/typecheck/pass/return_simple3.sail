function __id forall 'n. (x: int('n)) -> int('n) = x

overload __size = {__id}

val return_test : forall ('N : Int), 'N >= 10. (implicit('N), range(10, 'N)) -> range(10, 'N)

function return_test(N, x) = {
  return(x);
  'N
}
