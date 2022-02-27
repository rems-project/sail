default Order dec

struct State('n: Int) = {
  N : bitvector('n, dec),
  Z : bitvector(1, dec)
}

register procState : State(1)

val myStateM : unit -> State(1) effect {undef}

function myStateM () = {
  r : State(1) = undefined;
  r.N = 0b1;
  r.Z = 0b1;
  r
}

let myState : State(1) = struct { N = 0b1, Z = 0b1 }

val test : unit -> unit effect {undef}

function test () = {
  myState1 : State(1) = undefined;
  myState2 : State(1) = struct { N = undefined, Z = 0b1 };
  myState3 : State(1) = { myState2 with N = 0b0 };
  ()
}
