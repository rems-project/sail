default Order dec

$include <prelude.sail>

register R : bool

val f : unit -> {'n, 1 <= 'n <= 3. int('n)}

function main((): unit) -> unit = {
  let _ = 0b1001[if R then 0 else f()];
  ()
}
