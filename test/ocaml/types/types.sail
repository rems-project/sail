enum signal = {Low, High}

enum enum_single = {SingleConstructor}

type byte = bits(8)

type b32 = bits(32)

type b64 = bits(64)

register R64 : b64

register R32 : b32

register R8 : byte

register SIGNALREG : signal

struct TestStruct = {
  field1 : bits(2),
  field2 : byte,
  field3 : bool
}

register SREG : TestStruct

register OREG : option(byte)

val main : unit -> unit effect {rreg, wreg}

function main () = {
  R8 = 0xFF;
  SIGNALREG = Low;
  print(if SIGNALREG == Low then "pass" else "fail");
  SIGNALREG = High;
  print(if SIGNALREG == High then "pass" else "fail");
  SREG.field1 = 0b00;
  print(if SREG.field1 == 0b00 then "pass" else "fail");
  SREG.field1 = 0b11;
  print(if SREG.field1 == 0b11 then "pass" else "fail");
  print("pass")
}
