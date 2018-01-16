val plus = {ocaml: "add", lem: "add"}: forall ('n : Int) ('m : Int).
  (atom('n + 20), atom('m)) -> atom('n + 20 + 'm)

val minus_ten_id = {ocaml: "id", lem: "id"}: forall ('n : Int), 'n <= -10.
  atom('n) -> atom('n)

val ten_id = {ocaml: "id", lem: "id"}: forall ('n : Int), 'n >= 10.
  atom('n) -> atom('n)

val branch : forall ('N : Int), 'N >= 63. range(10, 'N) -> range(10, 'N)

function branch x = match x {
  y : range(10, 30) => y,
  _ : atom(31) => 'N,
  _ : range(31, 40) => plus(60, 3)
}
and branch _ : range(51, 63) = ten_id('N)
