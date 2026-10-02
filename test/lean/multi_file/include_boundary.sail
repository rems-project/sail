val before : unit -> int
function before() = 1
$include "inputs/register.sail"
val after : unit -> int
function after() = before()
