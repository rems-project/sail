default Order dec

val "print_endline" : string -> unit

struct S('a: Type) = {
  field1 : 'a,
  field2 : unit
}

function f forall ('a :Type). (s: S('a)) -> unit = {
  s.field2
}

function main((): unit) -> unit = {
  let s : S(unit) = struct { field1 = (), field2 = () };
  f(s);
  print_endline("ok");
}
