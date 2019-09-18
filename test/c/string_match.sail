default Order dec

$include <prelude.sail>
$include <mapping.sail>

function main() -> unit =
  match "Hello,_World" {
    "Hello" ^ x ^ "World" => {
      print_endline("matched");
      print_endline(x);
    },
    _ => print_endline("failed")
  }
