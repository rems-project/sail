
function forall Nat 'n, 'n IN {1,2,3}. bool test (([:'n:]) x) =
{
  true
}

let x = test(1)
let y = test(3)
let z = test(4)