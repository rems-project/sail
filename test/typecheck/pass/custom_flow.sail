val print_endline = pure "print_endline" : string -> unit

val operator <= = pure {
  coq: "Z.leb",
  _: "lteq"
} : forall 'n 'm. (int('n), int('m)) -> bool('n <= 'm)

function test1 forall 'n 'm. (n: int('n), m: int('m)) -> unit = {
  if n <= m then {
    _prove(constraint('n <= 'm));
    print_endline("1");
  } else {
    print_endline("2");
    _prove(constraint('n > 'm));
  }
}

val and_bool = pure {
  coq: "andb",
  _: "and_bool"
} : forall ('p: Bool) ('q: Bool). (bool('p), bool('q)) -> bool('p & 'q)

overload operator & = {and_bool}

function test2 forall 'n 'm. (n: int('n), m: int('m)) -> unit = {
  let x = n <= m & n <= 20;
  if x then {
    _prove(constraint('n <= 20));
    _prove(constraint('n <= 'm));
    print_endline("3")
  } else {
    _prove(constraint('n > 'm | 'n > 20));
    print_endline("4")
  }
}

function main((): unit) -> unit = {
  test1(1, 2);
  test1(2, 1);
  test2(1, 2);
  test2(2, 1);
  test2(21, 0)
}
