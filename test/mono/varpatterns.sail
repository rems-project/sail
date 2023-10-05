default Order dec
$include <prelude.sail>

/* Test constant propagation on some variable patterns in let expressions */

val test : bool -> unit

function test(b) = {
    let 'n : {|8,16|} = if b then 8 else 16;
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    assert(unsigned(x) == (match n { 8 => 18, 16 => 4660 }) : int, "unsigned");
}

val test2 : bool -> unit

function test2(b) = {
    let 'n = (if b then 8 else 16) : {|8,16|};
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    assert(unsigned(x) == (match n { 8 => 18, 16 => 4660 }) : int, "unsigned");
}

val test_mult : {|4,8|} -> unit

function test_mult('m) = {
    let 'n = 2 * 'm;
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    assert(unsigned(x) == (match n { 8 => 18, 16 => 4660 }) : int, "unsigned");
}

val run : unit -> unit

function run() = {
    test(true);
    test(false);
    test2(true);
    test2(false);
    test_mult(4);
    test_mult(8);
}
