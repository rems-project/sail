
val forall Nat 'N. [|10:'N|] -> [|10:'N|] effect pure return_test

function forall Nat 'N. [|10:'N|] return_test x =
{
  return x;
  return x;
  return x;
  return x;
  x
}
