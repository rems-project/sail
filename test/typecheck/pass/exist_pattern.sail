default Order inc

register nat n
register nat x
register nat y

val (int, int) -> bool effect pure eq_int

overload (deinfix ==) [eq_int]

typedef wordsize = exist 'n, 'n IN {8,16,32}. [|'n|]
let (wordsize) word = ([|8|]) 8

function nat main () = {

  (* works - x and y are set to 42 *)
  n := 1;
  y :=
  (switch n {
    case 0 -> { x := 21; x }
    case 1 -> { x := 42; x }
    case z -> { x := 99; x }
  });

  switch word {
    case ([|8|]) 8 -> { x:= 32; }
    case ([|16|]) 16 -> { x:= 64; }
    case ([|32|]) 32 -> { x:= 128; }
  };

  switch 0b010101 {
    case (0b01:(bit[1]) _:0b101) -> n:= 42
    case _ -> n:=0
  };

  n := 3;
  switch n {
    case 0 -> { 21 }
    case 1 -> { 42 }
    case u -> { 99 }
  };
}
