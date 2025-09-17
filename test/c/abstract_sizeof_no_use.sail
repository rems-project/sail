default Order dec

$include <prelude.sail>

type xlen : Int

constraint xlen in {32, 64}

$iftarget c cpp
$c_in_main sail_set_abstract_xlen(32);
$else
$option --instantiate xlen=32
$endif

function main() -> unit = {
  print_endline(dec_str(sizeof(xlen)));
}
