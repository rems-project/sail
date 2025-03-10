default Order dec

$include <prelude.sail>

struct my_struct = {
  field1 : int,
  field2 : string,
}

val example1 : unit -> unit

function example1() = {
  let v : my_struct = config some.json_struct;
  print_endline(v.field2);
}

union my_union = {
  Constructor1 : int,
  Constructor2 : string,
}

val example2 : unit -> unit

function example2() = {
  let v : my_union = config some.json_union;
  match v {
    Constructor1(n) => print_int("Got integer ", n),
    Constructor2(message) => print_endline(message),
  }
}
