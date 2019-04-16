default Order dec

$include <prelude.sail>

function id(c: bits(64)) -> bits(64) = c

function g(c__arg: bits(64), c': bits(64)) -> bool = {
  c = c__arg;
  c == c'
}

function f(c: bits(64), c': bits(64)) -> bool = {
  let c = c;
  g(c', c)
}

$property
function prop(c: bits(64)) -> bool = {
  f(c, c) & g(c, c)
}