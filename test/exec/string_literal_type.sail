default Order dec

$include <prelude.sail>

$option -string_literal_type

val test : string_literal -> unit

function test(s) = print_endline(s)

val main : unit -> unit

function main() = {
  let x : string_literal = "foo";
  var y : string_literal = "bar";
  let z = "baz";
  y = x;
  print_endline(y);
  test(y);
  y = z;
  print_endline(y);
  test(y);
  match x {
    "foo" => print_endline("ok"),
    _ => print_endline("fail"),
  };
  match y {
    "baz" => print_endline("ok"),
    _ => print_endline("fail"),
  };
  match concat_str(x, z) {
    "foobaz" => print_endline("ok"),
    _ => print_endline("fail"),
  }
}
