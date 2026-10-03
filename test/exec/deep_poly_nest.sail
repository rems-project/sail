default Order dec

$include <prelude.sail>

// Mostly to test that prover backends can handle a Nat -> Int
// conversion nested deeply in a polymorphic type.

struct wrapper('a) = { wrapped : 'a }

type foo('a) = list(option(wrapper(list(option(wrapper(list(option(wrapper('a)))))))))

let bar : foo(nat) = [|Some(struct { wrapped = [|Some (struct { wrapped = [|Some (struct { wrapped = 3 })|] })|] })|]

val baz : foo(int) -> unit

function baz(xs) = {
  match xs {
    Some(struct { wrapped = ys }) :: _ => print_endline("ok"),
    _ :: _ => (),
    [||] => (),
  }
}

val main : unit -> unit

function main() = {
  let quux : list(option(wrapper(list(option(wrapper(list(option(wrapper(int(7)))))))))) = [|None()|];
  baz(quux);
  baz(bar);
}
