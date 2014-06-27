function nat id ( n ) = n

register (bit[5]) c

function unit f() = {
 (if( true ) then 
   a := (nat) (3 + 0b01) mod 4
  else 
   a := 4
 );
 c := (bit[5]) (3 + 0b00001) mod 2;
 b := a;
}

function nat effect pure main _ = {
  f();
  id(42);
}
