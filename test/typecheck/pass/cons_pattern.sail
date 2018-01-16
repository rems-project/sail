val test : list(bit) -> unit

function test xs = match xs {
  x :: xs => (),
  [||] => ()
}
