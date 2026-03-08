default Order dec
$include <prelude.sail>
$include <string.sail>

val list_test : list(int) -> unit

function list_test(xs) =
  match xs {
    x :: xs => {
      print_endline(".");
      list_test(xs)
    },
    [||] => print_endline("end")
  }

val main : unit -> unit

function main() = {
  list_test([||]);
  list_test([|1, 2, 3|])
}
