default Order dec

struct State('a: Type, 'n: Int) = {
  N : vector('n, dec, 'a),
  Z : vector(1, dec, bit)
}

register procState : State(bit, 1)

val myStateM : unit -> State(bit, 1) effect {undef}

function myStateM () = {
  r : State(bit, 1) = undefined;
  r.N = 0b1;
  r.Z = 0b1;
  r
}

let myState : State(bit, 1) = struct { N = 0b1, Z = 0b1 }

val test : unit -> unit effect {undef}

function test () = {
  myState1 : State(bit, 1) = undefined;
  myState2 : State(bit, 1) = struct { N = undefined, Z = 0b1 };
  myState3 : State(bit, 1) = { myState2 with N = 0b0 }
}
