default Order dec
$include <prelude.sail>

/* Functions which return
   1. a straightforward existential, which should be translation to a dependent pair
   2. a parametric function that gets instantiated by something that will be a dependent pair
   3. a function where the inferred result type is existential because of one of the arguments,
      but which shouldn't be a dependent pair.

   2 isn't supported at the moment because the type checker unpacks all of the existentials in
   the argument, so it's difficult to tell apart from 3.
 */

val f : int -> {'n, 'n > 0. (int('n), bits('n))}

function f(x) =
  if x > 0 then (x, sail_ones(x))
  else (1, 0b0)

function use_f() -> unit = {
  let x = 5;
  let (xx, xv) = f(x);
  assert(xx == 5);
  assert(xv == 0b11111);
  let y = -5;
  let (yy, yv) = f(y);
  assert(yy == 1);
  assert(yv == 0b0);
}

/* Not supporting for now

val snd : forall ('s 't : Type). ( ('s, 't) ) -> 't
function snd( (_, t) ) = t

function use_snd() -> unit = {
  let x : (int, bits(8)) = (10, 0x23);
  assert(snd(x) == 0x23);
  let y : (int, {'n, 8 >= 'n > 0. bits('n)}) = (11, 0x45);
  assert(sail_zero_extend(snd(y), 8) == 0x45);
}
*/

val g : forall 'n, 'n > 0. int('n) -> bits('n)

function g(n) = sail_ones(n)

function g_size() -> {'n, 'n > 0. int('n)} = 8

function use_g() -> unit = {
  assert(unsigned(g(g_size())) : int == 255);
}
