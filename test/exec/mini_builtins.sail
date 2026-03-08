// A small selection of the builtins tests that can easily be run in CI
// Taken from the builtins directory - anything added here (and there are
// obvious gaps) probably ought to be added there.
default Order dec
$include <prelude.sail>
$include <smt.sail>

overload zero_extend = {sail_zero_extend}

function test_add_bits() -> unit = {
  assert(64=^0x0 + 64=^0x0 == 64=^0x0);
  assert(64=^0x10000b4 + 64=^0xffffffffffffffec == 64=^0x10000a0);
  assert(64=^0x14001dc + 64=^0x8 == 64=^0x14001e4);
}

function test_append() -> unit = {
  assert(0=^0x0 @ 64=^0x10000cc == 64=^0x10000cc);
  assert(1=^0x0 @ 5=^0x1e == 6=^0x1e);
  assert(36=^0xfffffffff @ 28=^0xec2138c == 64=^0xfffffffffec2138c);
  assert(38=^0x1ce @ 14=^0x530 == 52=^0x738530);
  assert(64=^0x381a7d8 @ 0=^0x0 == 64=^0x381a7d8);
}

function test_clz() -> unit = {
  assert(count_leading_zeros(0x0) == 4);
  assert(count_leading_zeros(0x1) == 3);
  assert(count_leading_zeros(0x4) == 1);
  assert(count_leading_zeros(0xf) == 0);
}

function test_ctz() -> unit = {
  assert(count_trailing_zeros(0x0) == 4);
  assert(count_trailing_zeros(0x1) == 0);
  assert(count_trailing_zeros(0x4) == 2);
  assert(count_trailing_zeros(0xf) == 0);
}

function test_divmod() -> unit = {
  assert(ediv_int(7, 5) == 1);
  assert(ediv_int(7, -5) == -1);
  assert(ediv_int(-7, 5) == -2);
  assert(ediv_int(-7, -5) == 2);
  assert(emod_int(7, 5) == 2);
  assert(emod_int(7, -5) == 2);
  assert(emod_int(-7, 5) == 3);
  assert(emod_int(-7, -5) == 3);
  assert(tdiv_int(7, 5) == 1);
  assert(tdiv_int(7, -5) == -1);
  assert(tdiv_int(-7, 5) == -1);
  assert(tdiv_int(-7, -5) == 1);
  assert(tmod_int(7, 5) == 2);
  assert(tmod_int(7, -5) == 2);
  assert(tmod_int(-7, 5) == -2);
  assert(tmod_int(-7, -5) == -2);
  assert(fdiv_int(7, 5) == 1);
  assert(fdiv_int(7, -5) == -2);
  assert(fdiv_int(-7, 5) == -2);
  assert(fdiv_int(-7, -5) == 1);
  assert(fmod_int(7, 5) == 2);
  assert(fmod_int(7, -5) == -3);
  assert(fmod_int(-7, 5) == 3);
  assert(fmod_int(-7, -5) == -2);
}

function test_get_slice_int() -> unit = {
  assert(get_slice_int(1, -16, 6) == 1=^0x1, "get_slice_int(1, -16, 6) == 1=^0x1");
  assert(get_slice_int(1, 23, 6) == 1=^0x0, "get_slice_int(1, 23, 6) == 1=^0x0");
  assert(get_slice_int(11, 1024, 0) == 11=^0x400, "get_slice_int(11, 1024, 0) == 11=^0x400");
  assert(get_slice_int(64, 75272, 0) == 64=^0x12608, "get_slice_int(64, 75272, 0) == 64=^0x12608");
}

function test_hex_str() -> unit = {
  assert(hex_str(14) == "0xe");
  assert(hex_str(243234802384) == "0x38a1ec8ad0");
  assert(hex_str_upper(15) == "0xF");
  assert(hex_str_upper(243234802384) == "0x38A1EC8AD0");
}

function test_mult_int() -> unit = {
  assert(mult_int(0, 28) == 0);
  assert(mult_int(1, 123126) == 123126);
  assert(mult_int(4, 13058667) == 52234668);
}

function test_not_bool() -> unit = {
  assert(not_bool(false) == true);
  assert(not_bool(true) == false);
}

function test_replicate_bits() -> unit = {
  assert(replicate_bits(1=^0x0, 0) == 0=^0x0, "replicate_bits(1=^0x0, 0) == 0=^0x0");
  assert(replicate_bits(1=^0x0, 34) == 34=^0x0, "replicate_bits(1=^0x0, 34) == 34=^0x0");
  assert(replicate_bits(1=^0x1, 43) == 43=^0x7ffffffffff, "replicate_bits(1=^0x1, 43) == 43=^0x7ffffffffff");
  assert(replicate_bits(16=^0xff, 4) == 64=^0xff00ff00ff00ff, "replicate_bits(16=^0xff, 4) == 64=^0xff00ff00ff00ff");
}

function test_set_slice_bits() -> unit = {
  assert(set_slice_bits(3, 1, 3=^0x0, 1, 1=^0x1) == 3=^0x2, "set_slice_bits(3, 1, 3=^0x0, 1, 1=^0x1) == 3=^0x2");
  assert(set_slice_bits(32, 1, 32=^0x18, 7, 1=^0x0) == 32=^0x18, "set_slice_bits(32, 1, 32=^0x18, 7, 1=^0x0) == 32=^0x18");
  assert(set_slice_bits(32, 1, 32=^0x20000000, 30, 1=^0x1) == 32=^0x60000000, "set_slice_bits(32, 1, 32=^0x20000000, 30, 1=^0x1) == 32=^0x60000000");
  assert(set_slice_bits(32, 16, 32=^0x0, 0, 16=^0x1c) == 32=^0x1c, "set_slice_bits(32, 16, 32=^0x0, 0, 16=^0x1c) == 32=^0x1c");
  assert(set_slice_bits(32, 32, 32=^0x12111111, 0, 32=^0x13111111) == 32=^0x13111111, "set_slice_bits(32, 32, 32=^0x12111111, 0, 32=^0x13111111) == 32=^0x13111111");
}

function test_shift() -> unit = {
  assert(sail_shiftright(0xDEADBEEF, 16) == 0x0000DEAD);
  assert(sail_shiftright(0xDEADBEEF, 4) == 0x0DEADBEE);
  assert(sail_arith_shiftright(0xDEADBEEF, 16) == 0xFFFFDEAD);
  assert(sail_arith_shiftright(0xDEADBEEF, 4) == 0xFDEADBEE);
  assert(sail_shiftleft(0xDEADBEEF, 16) == 0xBEEF0000);
  assert(sail_shiftleft(0xDEADBEEF, 4) == 0xEADBEEF0);
}

function test_shl_int() -> unit = {
  assert(shl_int(1, 5) == 32);
  assert(shl_int(8, 2) == 32);
  assert(shl_int(16,    -4) == 1);
}

function test_signed() -> unit = {
  assert(signed(zero_extend(0x10000, 32)) == 65536);
  assert(signed(zero_extend(0x17ffe, 32)) == 98302);
  assert(signed(zero_extend(0x80000003, 32)) == -2147483645);
  assert(signed(zero_extend(0x8899aabb8899aabd, 64)) == -8603657890687243587);
}

function test_slice_mask() -> unit = {
  assert(slice_mask(32, 8, 4)   == 0x00000F00);
  assert(slice_mask(32, 16, 8)  == 0x00FF0000);
  assert(slice_mask(32, 15, 3)  == 0x00038000);
  assert(slice_mask(32, 16, 32) == 0xFFFF0000);
}

function test_sub_int() -> unit = {
  assert(sub_int(0, 0) == 0);
  assert(sub_int(0, 14) == -14);
  assert(sub_int(10, 17) == -7);
  assert(sub_int(45, 19) == 26);
}

function test_unsigned() -> unit = {
  assert(unsigned(zero_extend(0x21adf4, 52)) == 2207220);
  assert(unsigned(zero_extend(0x140, 64)) == 320);
  assert(unsigned(zero_extend(0x2e01580, 64)) == 48240000);
  assert(unsigned(zero_extend(0xa5a5a5a5a5a5a5a5, 64)) == 11936128518282651045);
  assert(unsigned(zero_extend(0xfffffffef89b3cde, 64)) == 18446744069290540254);
}

function test_vector_update() -> unit = {
  v = 0x0BEEF0;
  v[0] = bitone;
  assert(v == 0x0BEEF1, "v == 0x0BEEF1");
  v[1] = bitone;
  assert(v == 0x0BEEF3, "v == 0x0BEEF3");
  v[4] = bitzero;
  assert(v == 0x0BEEE3, "v == 0x0BEEE3");
}

function test_vector_update_subrange() -> unit = {
  v = 0x0BEEF0;
  v[19 .. 4] = 0xDEAD;
  assert(v == 0x0DEAD0, "v == 0x0DEAD0");
  v[0 .. 0] = 0b1;
  assert(v == 0x0DEAD1, "v == 0x0DEAD1");
  v[1 .. 0] = 0b11;
  assert(v == 0x0DEAD3, "v == 0x0DEAD3");
}

function main() -> unit = {
  test_add_bits();
// Currently a problem with Lean
  test_append();
  test_clz();
  test_ctz();
  test_divmod();
  test_get_slice_int();
  test_hex_str();
  test_mult_int();
  test_not_bool();
  test_replicate_bits();
  test_set_slice_bits();
  test_shift();
  test_shl_int();
  test_signed();
  test_slice_mask();
  test_sub_int();
  test_unsigned();
  test_vector_update();
  test_vector_update_subrange();
}
