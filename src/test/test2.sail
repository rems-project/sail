
function unit f() = {
 (if( true ) then 
   a := (nat) (3 + 0b01) mod 4
  else 
   a := 4
 );
 a:= (nat) 0b010101;
 a:= (nat) (0b0101010 + 0b0101000);
 c := (bit[5]) (3 + 0b00101) mod 3;
 if c[1] then c:= 31 else c:= 0;
 b := a;
}


