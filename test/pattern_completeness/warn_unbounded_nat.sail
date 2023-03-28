default Order dec

$option -dpattern_warning_no_literals

function foo(x: nat) -> unit = {
    match x {
        0 => (),
        1 => (),
        2 => (),
        3 => (),
    }
}
