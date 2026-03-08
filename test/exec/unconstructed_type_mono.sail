$include <result.sail>
$include <string.sail>

union U ('a: Type) = { U1 : 'a }

type V = U(unit)

val main : unit -> unit
function main () = let r : result(V, unit) = Err(()) in print_endline("ok")
