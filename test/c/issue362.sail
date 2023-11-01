$include <result.sail>
$include <string.sail>

union P ('a: Type) = { P1 : 'a }
union U = { U1 : P(unit) }
type T = result({'n, 'n > 0. (U, int('n))}, unit)

val main : unit -> unit
function main () = let _ : T = Err(()) in print_endline("ok")
