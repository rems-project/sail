default Order dec

$include <prelude.sail>
$include <generic_equality.sail>
$include <exception.sail>

$option -undefined_gen

val decode : bits(32) -> unit

overload operator - = {sub_bits}
overload operator ^ = {xor_vec}

union clause exception = Reserved : string
union clause exception = Invalid_instruction : string

register VLEN : bits(2)

val vlen_length : unit -> {|64, 128, 256, 512|}

function vlen_length() = match VLEN {
    0b00 => 64,
    0b01 => 128,
    0b10 => 256,
    0b11 => 512,
}

type vlenmax: Int = 512

val split : forall 'len 'n 'm, 'len == 'n * 'm & 'n > 0 & 'm > 0.
    (int('n), int('m), bits('len)) -> vector('n, dec, bits('m))

function split(n, m, bv) = {
    var result: vector('n, dec, bits('m)) = undefined; 
    foreach (i from 1 to n) {
        result[i - 1] = bv[i * m - 1 .. i * m - m]
    };
    result
}

val merge : forall 'n 'm, 'n > 0 & 'm > 0. (int('n), int('m), vector('n, dec, bits('m))) -> bits('n * 'm)

function merge(n, m, vec) = {
    var result: bits('n * 'm) = sail_zeros(n * m);
    foreach (i from 1 to n) {
        result[i * m - 1 .. i * m - m] = vec[i - 1]
    };
    result
}

register V0 : bits(vlenmax)
register V1 : bits(vlenmax)
register V2 : bits(vlenmax)
register V3 : bits(vlenmax)

type vregindex = bits(2)

val set_V : (vregindex, bits(vlenmax)) -> unit

function set_V(i, bv) = match i {
    0b00 => V0 = bv,
    0b01 => V1 = bv,
    0b10 => V2 = bv,
    0b11 => V3 = bv,
}

val get_V : vregindex -> bits(vlenmax)

function get_V(i) = match i {
    0b00 => V0,
    0b01 => V1,
    0b10 => V2,
    0b11 => V3,
}

overload V = {set_V, get_V}

enum VectorOp = Vadd | Vsub | Vxor

val decode_vector_op : bits(2) -> VectorOp

function decode_vector_op(bv) = match bv {
    0b00 => Vadd,
    0b01 => Vsub,
    0b10 => Vxor,
    0b11 => throw Reserved("vector op 0b11"),
}

val vector_op : forall 'n 'm, 'n > 0 & 'm > 0.
    (VectorOp, int('n), int('m), vector('n, dec, bits('m)), vector('n, dec, bits('m))) -> vector('n, dec, bits('m))

function vector_op(op, n, m, v1, v2) = {
    var result: vector('n, dec, bits('m)) = undefined; 
    foreach (i from 0 to (n - 1)) {
        result[i] = match op {
            Vadd => v1[i] + v2[i],
            Vsub => v1[i] - v2[i],
            Vxor => v1[i] ^ v2[i],
        }
    };
    result
}

val decode_split : forall 'vlen, 'vlen in {64, 128, 256, 512}. (int('vlen), bits(4)) -> {'n 'm, 'vlen == 'n * 'm & 'm > 0. (int('n), int('m))}

function decode_split(vlen, splitting) = {
    match splitting {
        0b0000 => (1, vlen),
        0b0001 => let x = tdiv_int(vlen, 2) in { assert(x * 2 == vlen); (2, x) },
        0b0010 => let x = tdiv_int(vlen, 4) in { assert(x * 4 == vlen); (4, x) },
        0b0011 => let x = tdiv_int(vlen, 8) in { assert(x * 8 == vlen); (8, x) },
        0b0100 => let x = tdiv_int(vlen, 16) in { assert(x * 16 == vlen); (16, x) },
        0b0101 => let x = tdiv_int(vlen, 32) in { assert(x * 32 == vlen); (32, x) },
        0b0110 => let x = tdiv_int(vlen, 64) in { assert(x * 64 == vlen); (64, x) },
        0b0111 if vlen > 64 => let x = tdiv_int(vlen, 128) in { assert(x * 128 == vlen); (128, x) },
        0b1000 if vlen > 128 => let x = tdiv_int(vlen, 256) in { assert(x * 256 == vlen); (256, x) },
        0b1001 if vlen > 256 => let x = tdiv_int(vlen, 512) in { assert(x * 512 == vlen); (512, x) },
        _ => throw Invalid_instruction("vector split encoding"),
    }
}

function clause decode splitting : bits(4) @ 0xFFFFF @ vop : bits(2) @ dest : vregindex @ src1 : vregindex @ src2 : vregindex = {
    let vop = decode_vector_op(vop);
    let vlen = vlen_length();
    let (n, m) = decode_split(vlen, splitting);
    let v1 = split(n, m, V(src1)[vlen - 1 .. 0]);
    let v2 = split(n, m, V(src2)[vlen - 1 .. 0]);
    let result = vector_op(vop, n, m, v1, v2);
    V(dest) = sail_zero_extend(merge(n, m, result), sizeof(vlenmax))
}

function clause decode _ = throw Reserved("instruction")

val main : unit -> unit

function main() = {
    if split(2, 4, 0xAB) == [0xA, 0xB] then {
        print_endline("ok")
    };
    if split(8, 1, 0x53) == [0b0, 0b1, 0b0, 0b1, 0b0, 0b0, 0b1, 0b1] then {
        print_endline("ok")
    };
    if merge(2, 4, split(2, 4, 0xAB)) == 0xAB then {
        print_endline("ok")
    };

    V0 = 0x0000_1100_2200_3300_4400_5500_6600_7700_8800_9900_AA00_BB00_CC00_DD00_EE00_FF00_FFFE_1100_2200_3300_4400_5500_6600_7700_8800_9900_AA00_BB00_CC00_DD00_EE00_FFFF;
    V1 = 0x0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001_0001;
    VLEN = 0b10; // 256

    // add V0 to V1 in 64 groups of 4, storing the result in V2
    decode(0b0110 @ 0xFFFFF @ 0b00 @ 0b10 @ 0b00 @ 0b01);
    // add V0 to V1 in 16 groups of 16, storing the result in V3
    decode(0b0100 @ 0xFFFFF @ 0b00 @ 0b11 @ 0b00 @ 0b01);
    
    print_bits("V2 = ", V2);
    print_bits("V3 = ", V3);

    VLEN = 0b11; // 512

    // add V2 to V3 as a single 512 bit value, storing the result in V2
    decode(0b0000 @ 0xFFFFF @ 0b00 @ 0b10 @ 0b10 @ 0b11);

    print_bits("V2 = ", V2);
}
