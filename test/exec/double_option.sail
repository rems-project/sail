default Order dec

$include <prelude.sail>
$include <string.sail>

union option2('a: Type) = {
  Some2: ('a, 'a),
  None2: unit
}

function main() -> unit = {
  match Some2(Some2(0x00, 0x00), Some2(0xFF, 0xFF)) {
    Some2(Some2(_, _), Some2(_, _)) => print_endline("Some2 Some2"),
    Some2(None2(), None2())         => print_endline("Some2 None2"),
    None2()                         => print_endline("None2"),
  }
}
