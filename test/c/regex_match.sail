default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

function main() -> unit =
  match "He^l[lo]X,   !YWorld" {
    "He^l[lo]" ^ x ^ y : regex(", +!") ^ z ^ "World" => {
      print_endline("matched");
      print_endline(x);
      print_endline(y);
      print_endline(z)
    },
    _ => {
      print_endline("failure")
    }
  }
