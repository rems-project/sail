default Order dec
$include <prelude.sail>

union exception = {
  Error_foo : unit,
  Error_bar : int
}

val f : int -> int effect {escape}

function f(n) = {
  try {
    let m : int = if n > 5 then n - 3 else throw(Error_bar(n)) in
    m + 1
  } catch {
    Error_bar(n) => n
  }
}
