default Order dec

$include <prelude.sail>

union List('a) = {
  Nil : unit,
  Cons : ('a, List('a)),
}

val list_length : forall ('a : Type). List('a) -> int

function list_length(xs) = {
  var n : int = 0;
  var ys = xs;
  var done : bool = false;
  while not_bool(done) do {
    match ys {
      Nil() => done = true,
      Cons(_, tl) => {
        ys = tl;
        n = n + 1
      },
    }
  };
  n
}

val main : unit -> unit

function main() = {
  // Destroying a very long list must not overflow the stack
  var xs : List(int) = Nil();
  var i : int = 0;
  while i < 1000000 do {
    xs = Cons(i, xs);
    i = i + 1
  };
  print_int("length = ", list_length(xs));
  let ys = xs;
  xs = Nil();
  print_int("length = ", list_length(ys));
  print_int("length = ", list_length(xs));
}
