
$include <arith.sail>

infixl 5 +++

overload operator +++ = {add_atom}
