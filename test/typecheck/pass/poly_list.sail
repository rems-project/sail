default Order dec

$include <prelude.sail>

function cons(x: int, xs: list(int)) -> list(int) = {
  x :: xs
}

function poly_cons forall ('a : Type). (x: 'a, xs: list('a)) -> list('a) = {
  x :: xs
}

function main((): unit) -> unit = {
  let _ = cons(1, [|2, 3, 4|]);
  let _ : list(int) = poly_cons(1, [|2, 3, 4|]);
  // TODO: This fails due to different order of instantiation
  // let _ = poly_cons(1 : int, [|2, 3, 4|]);
  ()
}
