val forall Nat 'N, 'N IN {8,16}. [:'N:] -> unit effect pure test

function rec forall Nat 'N, 'N IN {8,16}. unit test (([:'N:]) x) =
{
  (nat) y := x;
  if y == 8
  then ()
  else test(y - 6)
}

let x = test(8)
let x = test(5)
