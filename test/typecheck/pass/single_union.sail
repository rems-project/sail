union foo = { BAR : int }

val f : foo -> int
function f BAR(x) = x

val g : foo -> int
function g x = match x { BAR(y) => y }

val h : int -> foo
function h x = BAR(x)
