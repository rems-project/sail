
register nat n 
register nat x
register nat y

typedef wordsize = forall Nat 'n, 'n IN {8,16,32}. [|'n|]
let forall Nat 'n. (wordsize<'n>) word = 8

function nat main _ = {

  (* works - x and y are set to 42 *)
  n := 1;
  y :=
  (switch n {
    case 0 -> { x := 21; x }
    case 1 -> { x := 42; x } 
    case z -> { x := 99; x }
  }); 

  switch word {
    case 8 -> { x:= 32; }
    case 16 -> { x:= 64; }
    case 32 -> { x:= 128; }
  };

  n := 3;
  switch n {
    case 0 -> { 21 }
    case 1 -> { 42 } 
    case x -> { 99 }
  };
}
