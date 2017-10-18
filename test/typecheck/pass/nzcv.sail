default Order dec

val bit[4] -> unit effect pure test

function test nzcv =
{
  N := 0b0;
  Z := 0b0;
  C := 0b0;
  V := 0b0;
  (N,Z,C,V) := nzcv;
  ()
}
