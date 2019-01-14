default Order dec

$include <prelude.sail>

// Check that the Coq backend correctly inserts autocasts.

// Here we need a cast after the call to concat to change 'n + 'm to 'm + 'n
val cast_result : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), bits('m)) -> bits('m + 'n)
function cast_result (v,w) = v @ w

/* FIXME: ought to cast result as if there were a type annotation
val no_call : forall 'n 'm, 'n > 0 & 'm > 0. bits('n + 'm) -> bits('m + 'n)
function no_call(v) = v
*/

val div_ex : forall 'n 'm, 'n > 0 & 'm > 0. (atom('n), bits('n * 'm)) -> bits('m)

// Here we need a cast before the call to div_ex to change 'n to 1*'n
val cast_arg : forall 'n, 'n > 0. bits('n) -> bits('n)
function cast_arg(v) = div_ex(1,v)

