default Order dec

struct State ('a : Type) = {
  N : vector(1, dec, 'a),
  Z : vector(1, dec, bit)
}

val myStateM : unit -> State(bit) effect {undef}

function myStateM () = {
  r : State(bit) = undefined;
  r.N = 0b1;
  r.Z = 0b1;
  r
}

let myState : State(bit) = struct { N = 0b1, Z = 0b1 }

val test : unit -> unit effect {undef}

function test () = {
  myState2 : State(bit) = struct { N = undefined, Z = 0b1 };
  myState3 : State(bit) = { myState2 with N = 0b0 }
}
