default Order inc

typedef option = const union forall Type 'a. {
    None;
    'a Some
}

function forall Type 'a. option<'a> none () = None

function forall Type 'a. option<'a> some (('a) x) = Some(x)

function forall Type 'a. int test ((option<'a>) x) =
{
  switch x {
    case None -> 0
    case (Some(y)) -> 1
  }
}

typedef either = const union forall Type 'a, Type 'b. {
  'a Left;
  'b Right
}

val forall Nat 'n, 'n >= 0. bit['n] -> int effect pure signed

function forall Type 'a, Type 'b. either<'a,'b> right (('b) x) = Right(x)

function int test2 ((either<int,bit[1]>) x) =
{
  switch x {
    case (Left(l)) -> l
    case (right(r)) -> signed(r)
  }
}
