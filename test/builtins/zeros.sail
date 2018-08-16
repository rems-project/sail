default Order dec

$include <exception_basic.sail>
$include <flow.sail>
$include <vector_dec.sail>

overload zeros = {sail_zeros}

function main (() : unit) -> unit = {
  assert(zeros(1)   == 1^0b0);
  assert(zeros(10)  == 10^0x0);
  assert(zeros(100) == 100^0x0);
  assert(zeros(102) == 102^0x0);
  assert(zeros(104) == 104^0x0);
  assert(zeros(106) == 106^0x0);
  assert(zeros(108) == 108^0x0);
  assert(zeros(110) == 110^0x0);
  assert(zeros(111) == 111^0x0);
  assert(zeros(112) == 112^0x0);
  assert(zeros(114) == 114^0x0);
  assert(zeros(116) == 116^0x0);
  assert(zeros(118) == 118^0x0);
  assert(zeros(120) == 120^0x0);
  assert(zeros(122) == 122^0x0);
  assert(zeros(124) == 124^0x0);
  assert(zeros(126) == 126^0x0);
  assert(zeros(128) == 128^0x0);
  assert(zeros(15)  == 15^0x0);
  assert(zeros(16)  == 16^0x0);
  assert(zeros(2)   == 2^0x0);
  assert(zeros(24)  == 24^0x0);
  assert(zeros(25)  == 25^0x0);
  assert(zeros(3)   == 3^0x0);
  assert(zeros(31)  == 31^0x0);
  assert(zeros(32)  == 32^0x0);
  assert(zeros(36)  == 36^0x0);
  assert(zeros(38)  == 38^0x0);
  assert(zeros(39)  == 39^0x0);
  assert(zeros(4)   == 4^0x0);
  assert(zeros(40)  == 40^0x0);
  assert(zeros(43)  == 43^0x0);
  assert(zeros(48)  == 48^0x0);
  assert(zeros(52)  == 52^0x0);
  assert(zeros(53)  == 53^0x0);
  assert(zeros(56)  == 56^0x0);
  assert(zeros(57)  == 57^0x0);
  assert(zeros(58)  == 58^0x0);
  assert(zeros(6)   == 6^0x0);
  assert(zeros(64)  == 64^0x0);
  assert(zeros(65)  == 65^0x0);
  assert(zeros(66)  == 66^0x0);
  assert(zeros(67)  == 67^0x0);
  assert(zeros(68)  == 68^0x0);
  assert(zeros(69)  == 69^0x0);
  assert(zeros(70)  == 70^0x0);
  assert(zeros(72)  == 72^0x0);
  assert(zeros(74)  == 74^0x0);
  assert(zeros(75)  == 75^0x0);
  assert(zeros(76)  == 76^0x0);
  assert(zeros(77)  == 77^0x0);
  assert(zeros(78)  == 78^0x0);
  assert(zeros(8)   == 8^0x0);
  assert(zeros(80)  == 80^0x0);
  assert(zeros(82)  == 82^0x0);
  assert(zeros(84)  == 84^0x0);
  assert(zeros(86)  == 86^0x0);
  assert(zeros(88)  == 88^0x0);
  assert(zeros(89)  == 89^0x0);
  assert(zeros(90)  == 90^0x0);
  assert(zeros(92)  == 92^0x0);
  assert(zeros(94)  == 94^0x0);
  assert(zeros(96)  == 96^0x0);
  assert(zeros(98)  == 98^0x0);
}