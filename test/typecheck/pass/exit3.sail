val test : forall ('a : Type). unit -> 'a effect {escape}

function test () = exit(())
