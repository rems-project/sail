register reg : range(0, 10)

val test : unit -> unit effect {wreg}

function test () = {
  reg = 9;
  reg = 10;
  reg = 8
}
