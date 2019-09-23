default Order dec

$include <prelude.sail>
$include <mapping.sail>

enum E = A | B | C

mapping test : token("[ABC]") <-> E = {
  "A" <-> A,
  "B" <-> B,
  "C" <-> C
}

mapping view : string <-> (E, E) = {
  x <- test() ^ y <- test() <-> (x, y)
}

function main() -> unit = {
  print_endline(view((A, B)))
}