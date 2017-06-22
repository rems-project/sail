
val forall Nat 'n, Nat 'l, Order 'o, Type 'a, 'l >= 0. (vector<'n,'l,'o,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access

default Order inc

val bit[4] -> unit effect pure test
    
function unit test v =
{
  z := vector_access(v,3);
  z := v[3]
}