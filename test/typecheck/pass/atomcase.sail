default Order dec

val extern forall Num 'n, Num 'm. (atom<'n>, atom<'m>) -> bool effect pure eq_atom
overload (deinfix ==) [eq_atom]

val forall 'n, 'n in {8,16}. [:'n:] -> int effect pure test_fn
val forall 'n, 'n in {8,16}. [:'n:] -> int effect pure test_switch

function test_fn 8 = 8
and test_fn 16 = 16


function test_switch n =
  switch(n) {
  case 8 -> 8
  case 16 -> 16
  }
 
