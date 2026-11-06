default Order dec

$include <prelude.sail>
$include <exception_basic.sail>

val main : unit -> unit

function main() = {
  if try throw Exception() catch { _ => true } then {
    print_endline("ok")
  }
}
