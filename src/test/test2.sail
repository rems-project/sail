function nat id ( n ) = n

function unit f() = {
 (if( true ) then 
   a := (nat) (3 + 0b01) mod 4
  else 
   a := 4
 );
 b := a;
}

function nat effect pure main _ = {
  f();
  id(42);
}
