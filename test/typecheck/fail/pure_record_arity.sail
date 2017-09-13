default Order dec

typedef State = const struct forall Type 'a, Nat 'n. {
  vector<0, 'n, dec, 'a> N;
  vector<0, 1, dec, bit> Z;
}

register State procState

let (State<bit,1>) myStateM = {
  (State<bit,1>) r := undefined;
  r.N := 0b1;
  r.Z := 0b1;
  r
}

let (State<bit,1>) myState = { N = 0b1; Z = 0b1 }

val unit -> unit effect {undef} test

function test () = {
  (State<bit,1>) myState1 := undefined;
  (State<bit,1>) myState2 := { N = undefined; Z = 0b1 };
  (State<bit,1>) myState3 := { myState2 with N = 0b0 }
}
