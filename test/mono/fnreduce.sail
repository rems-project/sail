(* Test constant propagation part of monomorphisation involving
   functions.  We should reduce a function application when the
   arguments are suitable values, the function is pure and the result
   is a value.
 *)

typedef AnEnum = enumerate { One; Two; Three }

typedef EnumlikeUnion = const union { First; Second }

typedef ProperUnion = const union {
  (AnEnum) Stuff;
  (EnumlikeUnion) Nonsense;
}

function AnEnum canReduce ((AnEnum) x) = {
  switch (x) {
  case One -> Two
  case x -> x
  }
}

function nat cannotReduce ((AnEnum) x) = {
  let (nat) y = switch (x) { case One -> 1 case _ -> 5 } in
  2 + y
}

function AnEnum effect {rreg} fakeUnpure ((AnEnum) x) = {
  switch (x) {
  case One -> Two
  case x -> x
  }
}

function EnumlikeUnion canReduceUnion ((AnEnum) x) = {
  switch (x) {
  case One -> First
  case _ -> Second
  }
}

function ProperUnion canReduceUnion2 ((AnEnum) x) = {
  switch (x) {
  case One -> Nonsense(First)
  case y -> Stuff(y)
  }
}

(* FIXME LATER: once effect handling is in place we should get an error
   because this isn't pure *)

val AnEnum -> (AnEnum,nat,AnEnum,EnumlikeUnion,ProperUnion) effect pure test

function test (x) = {
  let a = canReduce(x) in
  let b = cannotReduce(x) in
  let c = fakeUnpure(x) in
  let d = canReduceUnion(x) in
  let e = canReduceUnion2(x) in
  (a,b,c,d,e)
}

val unit -> bool effect pure run

function run () = {
  test(One) == (Two,3,Two,First,Nonsense(First)) &
  test(Two) == (Two,7,Two,Second,Stuff(Two)) &
  test(Three) == (Three,7,Three,Second,Stuff(Three))
}
