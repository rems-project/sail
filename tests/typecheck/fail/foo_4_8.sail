val forall Nat 'n, 'n IN {8}. [:'n:] -> unit effect pure Foo8
val forall Nat 'n, 'n IN {4}. [:'n:] -> unit effect pure Foo4
function forall Nat 'n, 'n IN {4,8}. unit Foo( ([:'n:]) x ) =
{
if sizeof 'n == 8
then  Foo8(x)
else
  Foo4(x);
Foo4(x)
}