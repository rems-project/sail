default Order dec

union Foo ('a : Type) = {
  MkFoo : { field1 : 'a, field2 : int }
}

val "print_endline" : string -> unit

function main((): unit) -> unit = {
  let _: Foo(unit) = MkFoo(struct { field1 = (), field2 = 22 });
  print_endline("ok")
}
