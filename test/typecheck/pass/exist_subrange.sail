default Order dec

val forall Num 'n, Num 'm, Num 'o (* , 'm >= 'o, 'o >= 0, 'n >= 'm + 1 *).
  (bit['n], [:'m:], [:'o:]) -> bit['m - ('o - 1)] effect pure vector_subrange

function unit test ((bit[6]) xs) =
{
  (int) len := 4;
  (exist 'n. [:'n:]) len := 5;
  ys := xs[len .. 0];
  ()
}
