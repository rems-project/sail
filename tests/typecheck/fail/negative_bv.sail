
function forall Nat 'n, Nat 'm, 'n <= 'm, 'n != 'm. bit['n - 'm] Zeros () =
{
  (bit['n - 'm]) 0
}

function unit test () =
{
  (bit[-1]) x := Zeros ();
  ()
}

function forall Nat 'n. range<0, 2** 'n> test2 ((bit['n]) x) =
{
  (range<0, 2** 'n>) x
}
