default Order dec

$include <prelude.sail>

$option --abstract-types
$option --instantiate b=true

type b : Bool

constraint b

val only_true : bool(true) -> unit

val test : bool(b) -> unit

function test(b) = {
  let x = b;
  only_true(x)
}
