// Tests for -mono_rewrites

default Order dec
$include <prelude.sail>

// The preconditions for this rewrite require a non-constant size somewhere, so
// pull the example out into a separate function.
val sign_ext_fun : forall 'z 'n, 'z >= 0 & 'n >= 4 + 'z. (bits(12), int('z), int('n)) -> bits('n)
function sign_ext_fun(y, z, n) = {
  sail_sign_extend(y[7..4] @ sail_zeros(z), n)
}

val run : unit -> unit effect {escape}

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
}
