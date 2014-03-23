function nat id ( n ) = n

function unit f() = {
 (if( true ) then 
   a := 3
  else 
   a := 4
 );
 b := a;
}

function nat effect pure main _ = {
  f();
  id(42);
}
