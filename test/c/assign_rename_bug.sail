default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>

$include <exception_basic.sail>

$option -undefined_gen

val sub_vec_int = {
  c: "sub_bits_int",
  _: "sub_vec_int"
} : forall 'n. (bits('n), int) -> bits('n)

overload operator - = {sub_vec_int}

val print_bits52: (string, bits(52)) -> unit

function print_bits52(str, x) = print_bits(str, x)

val main : unit -> unit effect {undef}

function main() = {
  let addr : bits(52) = 0xF_FF00_0000_0000;
  i : int = undefined;
  size : int = 7;
  ret : unit = ();
  foreach (i from 1 to size by 1 in inc) {
    ret = print_bits("", addr + i);
    ret = print_bits52("", addr + i);
    ret = print_bits("", addr - i);
    ret = print_bits52("", addr - i);
  };
  return ret
}
