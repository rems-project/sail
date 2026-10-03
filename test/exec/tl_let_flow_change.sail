default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_int plen;
$c_in_main CREATE_OF(sail_int, mach_int)(&plen, 32);
$c_in_main sail_set_abstract_plen(plen);
$c_in_main_post KILL(sail_int)(&plen);
$c_in_main sail_set_abstract_xlen(64);
$else
$option --instantiate plen=32 --instantiate xlen=64
$endif

type plen : Int
let plen = sizeof(plen)
constraint plen >= 1

type xlen : Int
constraint xlen in {32, 64}
let xlen = sizeof(xlen)

function main() -> unit = {
  assert(xlen >= plen);
  assert(xlen >= plen);
  print_endline("ok")
}
