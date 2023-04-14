default Order dec

$include <prelude.sail>

val foo : list(bits(1)) -> unit

function foo(x) = {
    match x {
        [||] => (),
        0b0 :: _ => (),
        0b1 :: _ => (),
    };
    match x {
        [||] => (),
        [|0b1|] => (),
        _ :: _ :: _ => (),
    }
}
