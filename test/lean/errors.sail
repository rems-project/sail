default Order dec

$include <prelude.sail>

register dummy : bit

function test_exit(b : bool) -> unit = {
    if b then exit()
    else ()
}

function test_assert(b : bool) -> bit = {
    assert(b, "b is false");
    bitone
}