/* Test a boolean type parameter.  Not sure that this is terribly useful,
   but it fills a gap in coverage... */

$include <prelude.sail>

union perhaps('b : Bool) = {No : unit, Yes : {'n, 'b. atom('n)}}

val foo : forall 'n. atom('n) -> perhaps('n >= 0)

function foo(n) =
  if n >= 0 then Yes(n) else No()
