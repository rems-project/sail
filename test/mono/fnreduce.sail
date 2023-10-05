$include <prelude.sail>
$include <generic_equality.sail>

/* Test constant propagation part of monomorphisation involving
   functions.  We should reduce a function application when the
   arguments are suitable values, the function is pure and the result
   is a value.
 */

enum AnEnum = One | Two | Three

union EnumlikeUnion = { First, Second }

union ProperUnion = {
  Stuff : AnEnum,
  Nonsense : EnumLikeUnion
}

val canReduce : AnEnum -> AnEnum

function canReduce (x) = {
  match (x) {
  One => Two,
  x => x
  }
}

val cannotReduce : AnEnum -> int

function cannotReduce (x) = {
  let y : int = match (x) { One => 1, _ => 5 } in
  2 + y
}

register whatever : int

val impure : AnEnum -> AnEnum

function impure (x) = {
  match (x) {
  One => Two,
  x => let _ = whatever in x
  }
}

val canReduceUnion : AnEnum -> EnumlikeUnion

function canReduceUnion (x) = {
  match (x) {
  One => First,
  _ => Second
  }
}

val canReduceUnion2 : AnEnum -> ProperUnion

function canReduceUnion2 (x) = {
  match (x) {
  One => Nonsense(First),
  y => Stuff(y)
  }
}


val test : AnEnum -> (AnEnum,int,AnEnum,EnumlikeUnion,ProperUnion)

function test (x) = {
  let a = canReduce(x) in
  let b = cannotReduce(x) in
  let c = impure(x) in
  let d = canReduceUnion(x) in
  let e = canReduceUnion2(x) in
  (a,b,c,d,e)
}

val run : unit -> unit

function run () = {
  assert(test(One) == (Two,3,Two,First,Nonsense(First)));
  assert(test(Two) == (Two,7,Two,Second,Stuff(Two)));
  assert(test(Three) == (Three,7,Three,Second,Stuff(Three)));
}
