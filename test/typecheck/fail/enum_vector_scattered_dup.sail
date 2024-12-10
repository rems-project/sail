default Order dec

$include <prelude.sail>

$[enum_vector E_members]
scattered enum E

enum clause E = A

enum clause E = B

let E_members : vector(1, E) = [A]

end E
