default Order dec
$include <prelude.sail>

union bar = {
  Hello : unit,
}

function g() -> bar = Hello()

enum foo = {Hello, World}

function f() -> foo = Hello

function main() -> unit = {
  let x = f();
  let y = g();
  ()
}
