default Order dec

$include <prelude.sail>
$include <exception_basic.sail>
$include <string.sail>

val test : bool -> bool

function test(t) = {
    try {
        if t then {
            return(true)
        } else {
            throw(Exception())
        }
    } catch {
        Exception() => return(false)
    }
}

val main : unit -> unit

function main() = {
   if test(true) then {
       print_endline("ok")
   };
   if not_bool(test(false)) then {
       print_endline("ok")
   }
}