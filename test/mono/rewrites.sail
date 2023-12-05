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

// Should become 0b1 @ slice_mask(...)
// We take a dummy bitvector argument because the rewrites on their own aren't enough for Lem to have
// a type for 'm + 'n.
val fixed_then_mask : forall 'm 'n, 'm >= 0 & 'n >= 0. (int('m), int('n), bits('m + 'n)) -> bits('m + 'n + 1)
function fixed_then_mask(m, n, _) = 0b1 @ sail_ones(m) @ sail_zeros(n)

val zero_ones : forall 'm, 'm > 0. int('m) -> bits('m)
function zero_ones(m) = 0b0 @ sail_ones(m - 1)

val zeros_ones : forall 'm 'n, 'm > 0 & 0 < 'n < 'm. (int('m), int('n)) -> bits('m)
function zeros_ones(m, n) = sail_zeros(m-n) @ sail_ones(n)

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
    assert(fixed_then_mask(4,4,0b00000000) == 0b111110000);
    assert(zero_ones(4) == 0b0111);
    assert(zeros_ones(4,3) == 0b0111);
    assert(zeros_ones(6,3) == 0b000111);
}
