$ifndef _PRELUDE
$define _PRELUDE

$include <flow.sail>

$ifdef _DEFAULT_DEC
$include <vector_dec.sail>
$else
$include <vector_inc.sail>
$endif

$include <arith.sail>

$include <option.sail>

$endif
