default Order dec

$include <prelude.sail>

/* Test returning an existential with a mixed boolean/integer
constraint */

val foo : forall ('n : Int) ('b : Bool).
  (bool('b), int('n)) -> {'m, 'b & 'm == 'n | not('b) & 'm == 3. int('m)}

function foo(b, n) = {
  if b then n else 3
}

/* We now allow type synonyms for kinds other that Type */

type implies('p: Bool, 'q: Bool) -> Bool = not('p) | 'q

infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = implies('p, 'q)

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)

val my_not = {coq: "negb", _: "not"} : forall ('p : Bool). bool('p) -> {('q : Bool), 'p <--> not('q). bool('q)}

/* This example mimics 32-bit ARM instructions where a flag in the
function argument restricts a type variable in a specific branch of
the code */

val test : forall ('n : Int) ('b : Bool), 0 <= 'n <= 15 & implies('b, 'n <= 14).
  (bool('b), int('n)) -> unit

function test(cond, n) = {
  if cond then {
    _prove(constraint('n <= 14))
  } else {
    ()
  };

  if my_not(cond) then {
    ()
  } else {
    _prove(constraint('n <= 13))
  }
}