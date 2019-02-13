$include <flow.sail>

type implies('p: Bool, 'q: Bool) -> Bool = not('p) | 'q

infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = implies('p, 'q)

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)

val tautologies :  forall ('p : Bool) ('q : Bool) ('r : Bool). (bool('p), bool('q), bool('r)) -> unit effect {escape}

function tautologies(p, q, r) = {
  _not_prove(constraint('p));
  _not_prove(constraint('q));
  _not_prove(constraint('r));

  // implication definition
  _prove(constraint(not('p) | 'q --> ('p --> 'q)));
  _prove(constraint(('p --> 'q) --> not('p) | 'q));
  _prove(constraint(('p --> 'q) <--> not('p) | 'q));

  // implication properties
  _prove(constraint('p --> 'p));
  _prove(constraint(('p --> 'q) & ('q --> 'r) --> ('p --> 'r)));
  _prove(constraint(('p --> 'q) & 'p --> 'q));

  _prove(constraint('p & 'q <--> 'q & 'p));
  _prove(constraint('p | 'q <--> 'q | 'p));
  _prove(constraint(('p <--> 'q) <--> ('q <--> 'p)));

  // excluded middle
  _prove(constraint('p | not('p)));

  // de Morgan
  _prove(constraint(not('p | 'q) <--> not('p) & not('q)));
  _prove(constraint(not('p & 'q) <--> not('p) | not('q)));

  // contradiction
  _prove(constraint('p & not('p) --> false));
  {
    assert(constraint('p & not('p)));
    _prove(constraint(false))
  };
  _not_prove(constraint(false));

  _prove(constraint(('p <--> 'q) & ('p | 'q) --> ('p & 'q)));
  _prove(constraint(('p & 'q --> 'r) <--> ('p --> 'q --> 'r)));

  {
    assert(constraint('p));
    _prove(constraint('p))
  };
  _not_prove(constraint('p));

  {
    assert(constraint('p));
    assert(constraint('p --> 'q));
    _prove(constraint('q));
    assert(constraint('q --> 'r));
    _prove(constraint('r))
  };
  _not_prove(constraint('q));
}