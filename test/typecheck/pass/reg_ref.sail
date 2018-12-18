register reg : range(0, 10)

val modify : register(range(0,10)) -> unit effect {wreg}

function modify (r) = {
  (*r) = 9;
  (*r) = 10;
  (*r) = 8
}

val test : unit -> unit effect {wreg}

function test () = modify(ref reg)
