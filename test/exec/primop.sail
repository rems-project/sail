default Order dec

$include <prelude.sail>

val big_four : unit -> int

function big_four() = 4

val main : unit -> unit

function main() = {
    print_int("", abs_int(-4));
    assert(abs_int(-4) == 4);
    assert(abs_int(4) == 4);
    assert(abs_int(negate(4)) == 4);
    assert(abs_int(-4) == big_four());
    assert(abs_int(big_four()) == big_four());
    assert(abs_int(negate(big_four())) == big_four());

    assert(count_leading_zeros(0x0) == 4);
    assert(count_leading_zeros(0x2) == 2);

    assert(max_int(2, 4) == 4);
    assert(min_int(2, 4) == 2);
    assert(min_int(-20, 20) == -20);

    print_endline("ok");
}
