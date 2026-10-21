default Order dec
$include <prelude.sail>

function main() -> unit = {
  var s1 = "Not ";
  s1 = concat_str(s1, "bad");

  var s2 = " bad";
  s2 = concat_str("Not", s2);

  print_endline(s1);
  print_endline(s2);
}
