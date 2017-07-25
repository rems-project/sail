default Order dec

typedef ProcState = const struct forall Num 'n.
{
  bit['n] N;
  bit[1] Z;
  bit[1] C;
  bit[1] V
}

register ProcState<2> PSTATE

function unit test () =
{
  PSTATE.N := 0b1
}
