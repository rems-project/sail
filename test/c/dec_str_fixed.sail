default Order dec

$include <prelude.sail>
$include <string.sail>

val main : unit -> unit

function main() = {
  print_endline(hex_str(64));
  print_endline(hex_str_upper(64));
  print_endline(dec_str(64));
}
