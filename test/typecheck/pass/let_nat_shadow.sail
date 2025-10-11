default Order dec

$include <prelude.sail>

val f : nat -> unit

val main : unit -> unit

function main() =
  let i : nat = 0 in
  let j =
    let k : nat = i + 1 in
    k
  in
  let _ = f(j) in
  print_int("j = ", j)
