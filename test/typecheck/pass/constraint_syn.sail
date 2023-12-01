default Order dec
$include <prelude.sail>

$option -abstract_types

type xlen : Int

constraint xlen in {32, 64}

type is_32 : Bool = xlen == 32

type s_xlen : Int = xlen

val test : (bool(is_32), bits(s_xlen)) -> unit

function test(b: bool(is_32), xs: bits(s_xlen)) -> unit = {
  ()
}

val main : unit -> unit

function main() = {
  if sizeof(xlen) == 32 then {
    test(true, 0xFFFF_FFFF)
  };
  if constraint(is_32) then {
    ()
  }
}
