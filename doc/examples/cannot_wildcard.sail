default Order dec
$include <prelude.sail>
$include <string.sail>
$include <option.sail>

/*!
Here the `0b1` literal in the `(Some(0b1), _)` case would need to be
replaced for an exhaustiveness checker without bitvector literals to
check the case where `x` and `y` are both `Some`, but this would
change the behavior when `x` is `Some` and `y` is `None`, hence a
wildcard cannot be inserted.
*/
function cannot_wildcard(x: option(bits(1)), y: option(bits(1))) -> unit = {
    match (x, y) {
        (Some(0b0), Some(_))   => print_endline("1"),
        (Some(0b1), Some(0b0)) => print_endline("2"),
        (Some(0b1), _)         => print_endline("3"),
        (Some(0b0), None())    => print_endline("4"),
        (None(), _)            => print_endline("5"),
    }
}
