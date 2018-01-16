val case_test : forall ('N : Int), 'N >= 10.
  (atom(10), range(10, 'N)) -> range(10, 'N)

function case_test (x, y) = match (x, y) {_ => x}
