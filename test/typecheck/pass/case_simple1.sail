
val forall Nat 'N. ([:10:], [|10:'N|]) -> [|10:'N|] effect pure case_test

function forall Nat 'N. [|10:'N|] case_test (x, y) =
{
  switch (x, y) {
    case _ -> y
  }
}
