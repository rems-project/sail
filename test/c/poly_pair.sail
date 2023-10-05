default Order dec

val print = "print_endline" : string -> unit

val eq_int = { lem: "eq", coq: "Z.eqb", _: "eq_int" } : (int, int) -> bool

union test('a : Type, 'b : Type) = {
  Ctor1 : ('a, 'b),
  Ctor2 : int
}

val main : unit -> unit

function main() = {
  let x = Ctor1(3, 2);
  match x {
    Ctor1(y, z) if eq_int(y, 3) => print("1"),
    _ => print("2")
  };
}
