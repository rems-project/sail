
typedef signal = enumerate {Low; High}

typedef enum_single = enumerate {SingleConstructor}

typedef byte = bit[8]
typedef b32 = bit[32]
typedef b64 = bit[64]

register b64 R64
register b32 R32
register byte R8

register signal SIGNALREG

typedef TestStruct = const struct {
  bit[2] field1;
  byte field2;
  bool field3
}

register TestStruct SREG

val unit -> unit effect {rreg, wreg} main

function main () = {
  R8 := 0xFF;
  SIGNALREG := Low;
  print(if SIGNALREG == Low then "pass" else "fail");
  SIGNALREG := High;
  print(if SIGNALREG == High then "pass" else "fail");
  SREG.field1 := 0b00;
  print(if SREG.field1 == 0b00 then "pass" else "faiL");
  SREG.field1 := 0b11;
  print(if SREG.field1 == 0b11 then "pass" else "faiL");
  print("pass")
}
