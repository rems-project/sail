(* Test monomorphisation control dependencies *)

default Order dec

val (bool,bool) -> unit effect pure f

function f(nosplit,split) = {
  if nosplit then {
    let (exist 'x, true. [:'x:]) 'x = if split then 16 else 32 in
    let (bit['x]) v = extz(0b0) in
    ()
  } else ()
}

val (bool,bool) -> unit effect pure g

function g(split,nosplit) = {
  (exist 'x, true. [:'x:]) x := 16;
  (exist 'y, true. [:'y:]) y := 16;
  if split then
    x := 32
  else
    ();
  if nosplit then
    y := 32
  else
    ();
  let (exist 'z, true. [:'z:]) 'z = x in
  let (bit['z]) v = extz(0b0) in
  ()
}

typedef exception = unit

val bool -> unit effect {escape} h

(* Note: we don't really need to split on b, but it's awkward to avoid.
   The important bit is not to overreact to the exception. *)
function h(b) = {
  let (exist 'x, true. [:'x:]) 'x =
    if b then 16 else throw () in
  let (bit['x]) v = extz(0b0) in
  ()
}
