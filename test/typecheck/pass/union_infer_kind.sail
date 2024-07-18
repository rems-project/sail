default Order dec

$include <prelude.sail>

union my_option('a) = {
  My_none : unit,
  Ny_some : 'a,
}

union test_union('a, 'b, 'c) = {
  A : list('a),
  B : bool('b),
  C : int('c),
}
