default Order dec
$include <prelude.sail>

val extz : forall 'm 'n, 'm >= 0 & 'n >= 0. (implicit('n), bits('m)) -> bits('n)
function extz(n, v) = sail_mask(n, v)

/* Test monomorphisation control dependencies */

val f : (bool,bool) -> unit

function f(nosplit,split) = {
  if nosplit then {
    let 'x : {'x, 'x >= 0. int('x)} = if split then 16 else 32 in
    let v : bits('x) = extz(0b0) in
    ()
  } else ()
}

val g : (bool,bool) -> unit

function g(split,nosplit) = {
  x : {'x, 'x >= 0. int('x)} = 16;
  y : {'y, 'y >= 0. int('y)} = 16;
  if split then
    x = 32
  else
    ();
  if nosplit then
    y = 32
  else
    ();
  let 'z : {'z, 'z >= 0. int('z)} = x in
  let v : bits('z)= extz(0b0) in
  ()
}

type exception = unit

val h : bool -> unit

/* Note: we don't really need to split on b, but it's awkward to avoid.
   The important bit is not to overreact to the exception. */
function h(b) = {
  let 'x : {'x, 'x >= 0. int('x)} =
    if b then 16 else throw () in
  let v : bits('x) = extz(0b0) in
  ()
}

// A common pattern in current Arm decode functions (where undefined is
// actually implementation defined)

val i : bool -> unit

function i(b) = {
  x : {16,32} = 16;
  if b then {
    x = 32;
  } else {
    if undefined then {
      x = 16;
    } else {
      throw ();
    }
  };
  let 'x = x;
  let v : bits('x) = extz(0b0) in
  ()
}

val run : unit -> unit

function run () = {
  assert(true);
  f(false,false);
  f(false,true);
  g(false,false);
  g(false,true);
  h(true);
  i(true);
}
