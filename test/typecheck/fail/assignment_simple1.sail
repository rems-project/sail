
val ([:10:], unit) -> [:10:] effect pure f

function [:10:] f (x, y) = x

val unit -> [:10:] effect pure test

function [:10:] test () =
{
  z := 9;
  z
}

val unit -> unit effect pure test2

function unit test2 () = x := 10
