
default Order inc

typedef option = const union forall Type 'a. {
  None;
  'a Some
  }

typedef Test = const union {
  A;
  B;
  C
}


function option<Test> test () = Some(C)
