
default Order dec

scattered typedef ast = const union forall Num 'datasize, Num 'destsize, Num 'regsize.

val forall Num 'datasize, Num 'destsize, Num 'regsize.
  ast<'datasize,'destsize,'regsize> -> unit effect pure execute

scattered function forall Num 'datasize, Num 'destsize, Num 'regsize. unit execute

union ast member (bit[8], bit['regsize]) test

union ast member int test2

function clause execute (test (x, y)) =
{
  return ()
}

end ast

end execute
