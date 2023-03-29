default Order dec

$include <prelude.sail>
$include <option.sail>

function cannot_wildcard(x: option(bits(1)), y: option(bits(1))) -> unit = {
    match (x, y) {
        (Some(0b0), Some(_))   => (),
        (Some(0b1), Some(0b0)) => (),
        (Some(0b1), _)         => (),
        (Some(0b0), None())    => (),
        (None(), _)            => (),
    }
}
