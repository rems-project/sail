default Order dec

$include <prelude.sail>
$include <hex_bits_signed.sail>

function main() -> unit = {
  assert(not_bool(hex_bits_signed_backwards_matches((1, ""))));
  assert(not_bool(hex_bits_signed_backwards_matches((2, ""))));
  assert(not_bool(hex_bits_signed_backwards_matches((3, ""))));
  assert(not_bool(hex_bits_signed_backwards_matches((4, ""))));

  assert(hex_bits_signed_backwards_matches((4, "-0x1")));
  assert(hex_bits_signed_backwards_matches((4, "-0x8")));

  assert(hex_bits_signed_1("-0x1") == 0b1);
  assert(hex_bits_signed_2("-0x1") == 0b11);
  assert(hex_bits_signed_3("-0x1") == 0b111);
  assert(hex_bits_signed_4("-0x1") == 0xF);
  assert(hex_bits_signed_5("-0x1") == 0b11111);

  assert(hex_bits_signed_1("-0x0") == 0b0);
  assert(hex_bits_signed_2("-0x0") == 0b00);
  assert(hex_bits_signed_3("-0x0") == 0b000);
  assert(hex_bits_signed_4("-0x0") == 0x0);
  assert(hex_bits_signed_5("-0x0") == 0b00000);

  assert(not_bool(hex_bits_signed_backwards_matches((1, "0x1"))));
  assert(hex_bits_signed_backwards((1, "0x1")) == 0b0);
  assert(hex_bits_signed_1("0x1") == 0b0);

  assert(hex_bits_signed_2("0x1") == 0b01);
  assert(hex_bits_signed_3("0x1") == 0b001);
  assert(hex_bits_signed_4("0x1") == 0x1);
  assert(hex_bits_signed_5("0x1") == 0b00001);

  assert(hex_bits_signed_1(0b0) == "0x0");
  assert(hex_bits_signed_1(0b1) == "-0x1");

  assert(hex_bits_signed_2(0b00) == "0x0");
  assert(hex_bits_signed_2(0b01) == "0x1");
  assert(hex_bits_signed_2(0b10) == "-0x2");
  assert(hex_bits_signed_2(0b11) == "-0x1");

  assert(hex_bits_signed_3(0b000) == "0x0");
  assert(hex_bits_signed_3(0b001) == "0x1");
  assert(hex_bits_signed_3(0b010) == "0x2");
  assert(hex_bits_signed_3(0b011) == "0x3");
  assert(hex_bits_signed_3(0b100) == "-0x4");
  assert(hex_bits_signed_3(0b101) == "-0x3");
  assert(hex_bits_signed_3(0b110) == "-0x2");
  assert(hex_bits_signed_3(0b111) == "-0x1");

  assert(hex_bits_signed_4(0x0) == "0x0");
  assert(hex_bits_signed_4(0x1) == "0x1");
  assert(hex_bits_signed_4(0x2) == "0x2");
  assert(hex_bits_signed_4(0x3) == "0x3");
  assert(hex_bits_signed_4(0x4) == "0x4");
  assert(hex_bits_signed_4(0x5) == "0x5");
  assert(hex_bits_signed_4(0x6) == "0x6");
  assert(hex_bits_signed_4(0x7) == "0x7");
  assert(hex_bits_signed_4(0x8) == "-0x8");
  assert(hex_bits_signed_4(0x9) == "-0x7");
  assert(hex_bits_signed_4(0xA) == "-0x6");
  assert(hex_bits_signed_4(0xB) == "-0x5");
  assert(hex_bits_signed_4(0xC) == "-0x4");
  assert(hex_bits_signed_4(0xD) == "-0x3");
  assert(hex_bits_signed_4(0xE) == "-0x2");
  assert(hex_bits_signed_4(0xF) == "-0x1");

  assert(hex_bits_signed_5(0b00000) == "0x0");
  assert(hex_bits_signed_5(0b00001) == "0x1");
  assert(hex_bits_signed_5(0b00010) == "0x2");
  assert(hex_bits_signed_5(0b00011) == "0x3");
  assert(hex_bits_signed_5(0b00100) == "0x4");
  assert(hex_bits_signed_5(0b00101) == "0x5");
  assert(hex_bits_signed_5(0b00110) == "0x6");
  assert(hex_bits_signed_5(0b00111) == "0x7");
  assert(hex_bits_signed_5(0b01000) == "0x8");
  assert(hex_bits_signed_5(0b01001) == "0x9");
  assert(hex_bits_signed_5(0b01010) == "0xa");
  assert(hex_bits_signed_5(0b01011) == "0xb");
  assert(hex_bits_signed_5(0b01100) == "0xc");
  assert(hex_bits_signed_5(0b01101) == "0xd");
  assert(hex_bits_signed_5(0b01110) == "0xe");
  assert(hex_bits_signed_5(0b01111) == "0xf");
  assert(hex_bits_signed_5(0b10000) == "-0x10");
  assert(hex_bits_signed_5(0b10001) == "-0xf");
  assert(hex_bits_signed_5(0b10010) == "-0xe");
  assert(hex_bits_signed_5(0b10011) == "-0xd");
  assert(hex_bits_signed_5(0b10100) == "-0xc");
  assert(hex_bits_signed_5(0b10101) == "-0xb");
  assert(hex_bits_signed_5(0b10110) == "-0xa");
  assert(hex_bits_signed_5(0b10111) == "-0x9");
  assert(hex_bits_signed_5(0b11000) == "-0x8");
  assert(hex_bits_signed_5(0b11001) == "-0x7");
  assert(hex_bits_signed_5(0b11010) == "-0x6");
  assert(hex_bits_signed_5(0b11011) == "-0x5");
  assert(hex_bits_signed_5(0b11100) == "-0x4");
  assert(hex_bits_signed_5(0b11101) == "-0x3");
  assert(hex_bits_signed_5(0b11110) == "-0x2");
  assert(hex_bits_signed_5(0b11111) == "-0x1");

  print_endline("ok")
}
