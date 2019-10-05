/* For checking that the rewriting pass to remove guards correctly notices
   that irrefutable patterns (e.g, (_,_) ) subsume wildcards.  For best
   results, check the test function evaluates to true. */

default Order dec

$include <prelude.sail>

enum enumsingle = A
enum enumdouble = B | C

val f : (int,enumsingle, enumdouble) -> int

function f(x,p,q) = {
  let a : int = match (x,p) { (x,_) if x > 0 => 1, _ => 2 };
  let b : int = match (x,p) { (x,A) if x > 0 => 1, _ => 2 };
  let c : int = match (x,q) { (x,_) if x > 0 => 1, _ => 2 };
  let d : int = match (x,q) { (x,B) if x > 0 => 1, _ => 2 };
  a + b + c + d
}

val two : forall ('t : Type). 't -> int

function two _ = 2

val f' : (int,enumsingle, enumdouble) -> int

function f'(x,p,q) = {
  let a : int = match (x,p) { (x,_) if x > 0 => 1, z => two(z) };
  let b : int = match (x,p) { (x,A) if x > 0 => 1, z => two(z) };
  let c : int = match (x,q) { (x,_) if x > 0 => 1, z => two(z) };
  let d : int = match (x,q) { (x,B) if x > 0 => 1, z => two(z) };
  a + b + c + d
}

union unionsingle = { D : int }
union uniondouble = { E : int, F : int }

val g : (int,unionsingle) -> int

function g(x,p) = {
  let a : int = match (x,p) { (x,_) if x > 0 => 1, _ => 2};
  let b : int = match (x,p) { (x,D(_)) if x > 0 => 1, _ => 2};
  let c : int = match (x,p) { (x,D(5)) if x > 0 => 1, _ => 2};
  a+b+c
}

val h : (int,uniondouble) -> int

function h(x,p) = {
  let a : int = match (x,p) { (x,_) if x > 0 => 1, _ => 2};
  let b : int = match (x,p) { (x,E(_)) if x > 0 => 1, _ => 2};
  let c : int = match (x,p) { (x,E(5)) if x > 0 => 1, _ => 2};
  a + b + c
}

val test : unit -> bool

function test () =
  f(0,A,B) == 8 &
  f(1,A,B) == 4 &
  f(0,A,C) == 8 &
  f(1,A,C) == 5 &
  f'(0,A,B) == 8 &
  f'(1,A,B) == 4 &
  f'(0,A,C) == 8 &
  f'(1,A,C) == 5 &
  g(0,D(0)) == 6 &
  g(0,D(5)) == 6 &
  g(1,D(0)) == 4 &
  g(1,D(5)) == 3 &
  h(0,E(0)) == 6 &
  h(0,E(5)) == 6 &
  h(0,F(5)) == 6 &
  h(1,E(0)) == 4 &
  h(1,E(5)) == 3 &
  h(1,F(5)) == 5
