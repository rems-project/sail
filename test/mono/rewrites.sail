// Tests for -mono_rewrites

default Order dec
$include <prelude.sail>
$include <mono_rewrites.sail>

// The preconditions for this rewrite require a non-constant size somewhere, so
// pull the example out into a separate function.
val sign_ext_fun : forall 'z 'n, 'z >= 0 & 'n >= 4 + 'z. (bits(12), int('z), int('n)) -> bits('n)
function sign_ext_fun(y, z, n) = {
  sail_sign_extend(y[7..4] @ sail_zeros(z), n)
}

val zero_subrange : forall 'n, 2 < 'n & 'n < 8. (int('n), bits(8)) -> bool
function zero_subrange(n, x) = x[n..2] == sail_zeros(n - 2 + 1)

val ones_subrange : forall 'n, 2 < 'n & 'n < 8. (int('n), bits(8)) -> bool
function ones_subrange(n, x) = x[n..2] == sail_ones(n - 2 + 1)

val run : unit -> unit

function run() = {
    let x : bits(12) = 0x123;
    let y : bits(12) = 0x987;
    let 'i = 7;
    let 'j = 4;
    let 'z = 8;
    assert(sail_zero_extend(x[7..4] @ sail_zeros(8), 32) == 0x00000200);
    assert(sign_ext_fun(x, z, 32) == 0x00000200);
    assert(sail_zero_extend(y[7..4] @ sail_zeros(8), 32) == 0x00000800);
    assert(sign_ext_fun(y, z, 32) == 0xfffff800);
    assert(sail_ones(i) @ sail_zeros(9) == 0xfe00);
    assert(zero_subrange(4, 0x00));
    assert(zero_subrange(4, 0b11100011));
    assert(ones_subrange(4, 0xff));
    assert(ones_subrange(4, 0b00011100));
    assert(not_bool(zero_subrange(4, 0xff)));
    assert(not_bool(zero_subrange(4, 0b11101011)));
    assert(not_bool(ones_subrange(4, 0x00)));
    assert(not_bool(ones_subrange(4, 0b00010100)));
}
