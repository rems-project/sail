/* Example from https://github.com/rems-project/sail/issues/47 where a variable
   name is mistakenly used at the type level, which wasn't caught before due to
   the lack of a well-formedness check on specs.  This is the corrected version.
   */

default Order dec
$include <prelude.sail>

let 'THIRTY_TWO : atom(32) = 32

val f : bits(32) -> bits('THIRTY_TWO)
