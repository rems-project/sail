default Order dec
$include <prelude.sail>

enum foo = {Hello, World}

function f() -> foo = Hello

union bar = {
  Hello : unit,
}

function g() -> bar = Hello()

function main() -> unit = {
  let x = f();
  let y = g();
  ()
}
