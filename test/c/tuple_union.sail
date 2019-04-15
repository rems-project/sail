default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

union U('a: Type) = {
  Ctor : 'a
}

type pair = (int, int)

function foo(x: U(pair)) -> unit = {
  match x {
    Ctor(y, z) => {
      print_int("y = ", y);
      print_int("z = ", z)
    }
  };
  match x {
    Ctor((y, z)) => {
      print_int("y = ", y);
      print_int("z = ", z)
    }
  };
  match x {
    Ctor(x) => match x {
      (y, z) => {
	print_int("y = ", y);
	print_int("z = ", z)
      }
    }
  };
  print_endline("")
}

function main((): unit) -> unit = {
  foo(Ctor(1, 2));
  foo(Ctor((3, 4)));
  let x = (5, 6);
  foo(Ctor(x));
  let x = Ctor(7, 8);
  foo(x);
  let x = Ctor(((9, 10)));
  foo(x);
  let x = (11, 12);
  foo(Ctor(x));
}
