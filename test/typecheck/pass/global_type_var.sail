$include <flow.sail>

let (size as 'size) : {|32, 64|} = 32

val zeros : forall 'n. atom('n) -> vector ('n, dec, bit)

val test : atom('size) -> unit

function test x =
  if x == 32 then {
    ()
  } else {
    let y : atom(64) = size in
    ()
  }

val test2 : unit -> atom('size)

function test2 () = size
