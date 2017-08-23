default Order dec

typedef State = const struct forall Type 'a. {
  vector<0, 1, dec, 'a> N;
  vector<0, 1, dec, bit> Z;
}

let (State<bit>) myStateM = {
  (State<bit>) r := undefined;
  r.N := 0b1;
  r.Z := 0b1;
  r
}

let (State<bit>) myState = { N = 0b1; Z = 0b1 }

val unit -> unit effect {undef} test

function test () = {
  (State<bit>) myState2 := { N = undefined; Z = 0b1 };
  (State<bit>) myState3 := { myState2 with N = 0b0 }
}
