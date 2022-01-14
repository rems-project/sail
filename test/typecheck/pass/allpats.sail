/* Not really *all* of the patterns, but enough to exercise the exhaustiveness
   checker for Coq output */

default Order dec
$include <prelude.sail>

enum anenum = {Athing, Bthing, Cthing}

union aunion = {Dthing: unit, Ething: anenum, Fthing: (anenum,int)}

struct arecord = {elone: anenum, eltwo: aunion}

val f : (anenum, aunion, arecord, vector(5,dec,int), bits(4),list(anenum)) -> unit

function f(a,b,c,d,e,g) = {
  match a {
  Athing => (),
  Bthing => (),
  Cthing => ()
  };
  match a {
  Athing => (),
  _ => ()
  };
  match a {
  Athing => (),
  Bthing => ()
  };
  match b {
  Dthing(()) => (),
  Ething(Athing) => (),
  Ething(Bthing) => (),
  Ething(Cthing) => (),
  Fthing(Athing,_) => (),
  Fthing(Bthing,_) => (),
  Fthing(Cthing,_) => ()
  };
  match b {
  Dthing(()) => (),
  Ething(Athing) => (),
  Ething(Bthing) => (),
  Ething(Cthing) => (),
  Fthing(Athing,_) => (),
  Fthing(Cthing,_) => ()
  };
  match b {
  Dthing(()) => (),
  Ething(Athing) => (),
  Ething(Bthing) => (),
  Ething(Cthing) => (),
  Fthing(Athing,_) => (),
  Fthing(_ as x,_) => ()
  };
  /* Um, no syntax for record patterns? */
  /* Vector patterns must be bits? */
  match e {
  [_,_,_,bitzero] => (),
  [_,_,_,_] => ()
  };
  match e {
  [_,_,_,bitzero] => ()
  };
  match e {
  [_,bitzero] @ (_ : bits(2)) => (),
  _ => ()
  };
  match e {
  [_,bitzero] @ (_ : bits(2)) => ()
  };
  match (a,b) {
  (Athing,Ething(Bthing)) => (),
  (_,Fthing(_,_)) => (),
  (_,Dthing(())) => (),
  (Bthing,_) => (),
  (Cthing,_) => ()
  };
  match (a,b) {
  (Athing,Ething(Bthing)) => (),
  (Athing,Ething(_)) => (),
  (_,Fthing(_,_)) => (),
  (_,Dthing(())) => (),
  (Bthing,_) => (),
  (Cthing,_) => ()
  };
  match g {
  [| |] => (),
  [| Athing, Bthing |] => (),
  _::_::_ => ()
  };
  match g {
  [| |] => (),
  [| Athing, _, Bthing |] => (),
  _::_::_::_ => ()
  };
  match g {
  [| |] => (),
  [| Athing, _, Bthing |] => (),
  _::_ => ()
  }
}