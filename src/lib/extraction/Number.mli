open Decimal
open Hexadecimal

type uint =
| UIntDecimal of Decimal.uint
| UIntHexadecimal of Hexadecimal.uint

type signed_int =
| IntDecimal of Decimal.signed_int
| IntHexadecimal of Hexadecimal.signed_int
