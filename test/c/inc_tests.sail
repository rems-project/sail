default Order inc

$include <prelude.sail>

register R : bits(5) = 0b00011

val test_reg : unit -> unit

function test_reg() = {
    assert(R == 0b00011);
    assert(R[4] == bitone);
    R = 0b10000;
    assert(R[0] == bitone);
    assert(R[4] == bitzero);
    R[0] = bitzero;
    assert(R == 0b00000);
    R[0 .. 2] = 0b111;
    assert(R == 0b11100);
    (*(ref R))[0] = bitzero;
}

val test_slice : unit -> unit

function test_slice() = {
    assert(slice(0b10000, 0, 3) == 0b100);
    assert(slice(0b10000, 0, 1) == 0b1);
    assert(slice(0b10000, 1, 4) == 0b0000);
    assert(slice(0b10100, 1, 4) == 0b0100);
    assert(slice(0b10011, 1, 4) == 0b0011);
}

val main : unit -> unit

function main() = {
    let x: bits(2) = 0b10;
    assert(x[0] == bitone);
    assert(x[1] == bitzero);
    assert(unsigned(x) == 2);
    assert(signed(x) == -2);
    print_endline("ok 1");

    let x: bits(2) = [bitone, bitzero];
    assert(x[0] == bitone);
    assert(x[1] == bitzero);
    assert(unsigned(x) == 2);
    assert(signed(x) == -2);
    print_endline("ok 2");

    let x: bits(4) = 0b1100;
    assert(x[0..1] == 0b11);
    assert(x[1..2] == 0b10);
    assert(x[2..3] == 0b00);
    assert(x[0..3] == x);
    match x {
      0b11 @ y => assert(y == 0b00),
      _ => print_endline("unreachable"),
    };
    match x {
      [_] @ y @ [_] => assert(y[0] == bitone),
      _ => print_endline("unreachable"),
    };
    assert([x with 0 = bitzero] == 0b0100);
    assert([x with 0 = bitzero][0] == bitzero);
    assert([x with 0 .. 1 = 0b00] == 0x0);
    assert([x with 1 .. 3 = 0b111] == 0xF);
    print_endline("ok 3");

    assert(sail_zero_extend(0b10, 4) == 0b0010);
    assert(sail_sign_extend(0b10, 4) == 0b1110);

    print_bits("0b100 == ", 0b100);
    print_bits("0b001 == ", 0b001);
    print_endline("ok 4");

    test_reg();
    print_endline("ok 5");

    test_slice();
    print_endline("ok 6");
}