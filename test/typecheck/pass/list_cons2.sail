function foo (i : int, l : list(int)) -> list(int) = i :: l

val bar : forall ('a : Type). unit -> list('a)

function bar () = [||]

function baz l : list(int) -> list(int) = l

function quux () -> list(int) = baz(bar ())
