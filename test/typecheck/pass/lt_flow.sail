val lt_flow : forall 'n 'm. (int('n), int('m)) -> bool('n <= 'm)

val test : unit -> bool(true)

function test() = lt_flow(1,10)
