default Order dec

struct State = {
  N : bitvector(1, dec),
  Z : bitvector(1, dec)
}

val myStateM : unit -> State effect {undef}

function myStateM () = {
  r : State = undefined;
  r.N = 0b1;
  r.Z = 0b1;
  r
}

let myState : State = struct { N = 0b1, Z = 0b1 }

val test : unit -> unit effect {undef}

function test () = {
  myState2 : State = struct { N = undefined, Z = 0b1 };
  myState3 : State = { myState2 with N = 0b0 };
  ()
}
