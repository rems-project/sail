default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>
$include <string.sail>

$include <exception_basic.sail>

val main : unit -> unit

function main() =
{
  /*
   * Expect "Outer handler"
   */
  try {
    try throw Exception()
    catch {
      /* Exception in catch guard will throw to outer handler */
      Exception() if { throw Exception(); false } => {
        assert(false, "Unreachable");
        throw Exception()
      },
      _ => assert(false, "Unreachable")
    }
  } catch {
    Exception() => print_endline("Outer handler")
  };
}
