default Order dec

$include <prelude.sail>
$include <mapping.sail>

infixl 5 ++

overload operator ++ = concat_str

$[jib_debug]
function main() -> unit = {
  match " " {
    spc() => print_endline("ok"),
    _ => print_endline("fail 1"),
  };
  match "" {
    spc() => print_endline("fail 2"),
    _ => print_endline("ok"),
  };
  match " not spaces" {
    spc() => print_endline("fail 3"),
    _ => print_endline("ok"),
  };
}
