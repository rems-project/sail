default Order dec

$include <prelude.sail>
$include <mapping.sail>

val test1 : string <-> (bool, int)

mapping test1 = {
  "foo" <-> (true, 3),
  "b" ^ "ar" <-> (false, 2)
}

val test2 : (bool, int) <-> string

mapping test2 = {
  (true, 3) <-> "f" ^ "oo",
  (false, 2) <-> "bar"
}

val test3 : string <-> int

mapping test3 = {
  "baz" ^ test1(true, 3) ^ "quux" <-> 6
}

val "print_endline" : string -> unit

function main((): unit) -> unit = {
  print_endline(test1(true, 3));
  print_endline(test1(false, 2));
  match test1("foo") {
    (true, _) => print_endline("got true"),
    _ => print_endline("fail")
  };

  print_endline(test2(true, 3));
  print_endline(test2(false, 2));
  match test2("foo") {
    (true, _) => print_endline("got true"),
    _ => print_endline("fail")
  };

  print_endline(test3(6));
  ()
}