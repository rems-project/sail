
val (unit, [:10:]) -> [:10:] effect pure f

function [:10:] f (x, y) = y

val unit -> [:10:] effect pure test

function [:10:] test () =
{
  f(z := 10, z)
}

val unit -> unit effect pure test2

function unit test2 () = x := 10
