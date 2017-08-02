
val int -> unit effect pure f1
val (int, int) -> unit effect pure f2
val (int, int, int) -> unit effect pure f3

overload f [f1; f2; f3]

val unit -> unit effect pure test

function test () =
{
  f(1);
  f(2, 3);
  f(4, 5, 6);
}
