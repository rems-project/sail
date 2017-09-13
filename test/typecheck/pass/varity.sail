
val int -> unit effect pure f1
val (int, int) -> unit effect pure f2
val (int, int, int) -> unit effect pure f3

function f1 (i1) = ()
function f2 (i1, i2) = ()
function f3 (i1, i2, i3) = ()

overload f [f1; f2; f3]

val unit -> unit effect pure test

function test () =
{
  f(1);
  f(2, 3);
  f(4, 5, 6);
}
