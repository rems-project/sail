default Order dec

$include <prelude.sail>

val print_str = impure "print_effect" : (string) -> unit

function foo() -> bits(16) = {
  let z = 0xFFFF | 0xABCD in
  0x0000 & z
}

function bar() -> bits(16) = {
  let z : bits(16) = 0xFFFF | 0xABCD in
  0x0000 & z
}

function baz() -> bits(16) = {
  print_str("baz");
  0x0000
}

