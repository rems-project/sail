default Order dec

val "print_endline" : string -> unit
val "print_int" : (string, int) -> unit

struct S('a: Type) = {
  field1 : ('a, 'a),
  field2 : unit
}

function main((): unit) -> unit = {
  var s : S(range(0, 3)) = struct { field1 = (0, 3), field2 = () };
  s.field1 = (1, 2);
  match s.field1 {
    (x, y) => {
      print_int("x = ", x);
      print_int("y = ", y);
    }
  };
  print_endline("ok");
}
