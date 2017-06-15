
val forall Nat 'N. [|10:'N - 1|] -> [|10:'N - 1|] effect pure return_test

function forall Nat 'N. [|10:'N - 1|] return_test x =
{
  return x;
  sizeof 'N
}
