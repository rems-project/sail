default Order dec

$include <prelude.sail>

register X : bits(16)

function shadows_register() -> unit = {
  var X : bits(32) = 0xFFFF_FFFF;
  ()
}
