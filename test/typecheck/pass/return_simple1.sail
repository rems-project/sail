val return_test : forall ('N : Int). range(10, 'N) -> range(10, 'N)

function return_test x = {
  return(x);
  x
}
