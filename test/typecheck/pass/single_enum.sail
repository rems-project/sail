enum foo = { BAR }

val f : foo -> int
function f BAR = 1

val g : foo -> int
function g x = match x { BAR => 1 }

val h : int -> foo
function h _ = BAR
