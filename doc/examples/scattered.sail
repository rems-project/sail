default Order dec

$include <prelude.sail>

$span start DECS
// We can declare scattered types, for either unions or enums
scattered union U

scattered enum E

// For scattered functions and mappings, we have to provide a type signature with val
val foo : U -> bits(64)

scattered function foo

val bar : E <-> string

scattered mapping bar
$span end

$span start CLAUSES
enum clause E = E_one

union clause U = U_one : bits(64)

function clause foo(U_one(x)) = x

mapping clause bar = E_one <-> "first member of E"
$span end

$span start ENDS
end E

end U

end foo

end bar
$span end
