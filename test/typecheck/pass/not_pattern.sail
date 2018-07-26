default Order dec

$include <prelude.sail>

let x : int = 5

val main : unit -> unit

function main() = {
  match x {
    ~(3) => (),
    _    => ()
  }
}