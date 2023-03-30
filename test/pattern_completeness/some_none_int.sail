default Order dec

$include <prelude.sail>
$include <option.sail>

function foo(x: option(int)) -> unit = match x {
    None() => (),
    Some(5) => (),
    Some(_) => (),
}
