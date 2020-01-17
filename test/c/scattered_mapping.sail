default Order dec

$include <prelude.sail>
$include <string.sail>
$include <mapping.sail>

val "print_endline" : string -> unit

val unit_str_map : unit <-> string
scattered mapping unit_str_map
val unit_str : unit -> string
function unit_str () = unit_str_map_forwards(())
mapping clause unit_str_map = () <-> "()"

function main () : unit -> unit = {
  print_endline(unit_str())
}
