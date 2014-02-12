
register nat n 
register nat x
register nat y

function nat main _ = {

  (* works - x and y are set to 42 *)
  n := 1;
  y :=
  (switch n {
    case 0 -> { x := 21; x }
    case 1 -> { x := 42; x } 
    case x -> { x := 99; x }
  }); 

  (* doesn't work - main returns 1 instead of 99 *)
  n := 3;
  switch n {
    case 0 -> { 21 }
    case 1 -> { 42 } 
    case x -> { 99 }
  };
}
