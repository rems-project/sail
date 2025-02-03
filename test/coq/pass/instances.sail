default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

// This was written to test the Coq backend's support for producing EqDecision and Countable
// instances.

struct st0 = {
  f01: int,
  f02: bool,
}

struct st ('a : Type) = {
  field1: int,
  field2: 'a,
  field3: st0,
}

union un ('a : Type) = {
  br1: {bf1: int, bf2: 'a},
  br2: st0,
}

type stalias1 = st(int)
type unalias1 = un(int)
type stalias2 ('t : Type) = st('t)
type unalias2 ('t : Type)= un('t)

register r1 : st(st0) = struct { field1 = 2, field2 = struct {f01 = 3, f02 = true}, field3 = struct {f01 = 4, f02 = false} }
register r2 : un(st0) = br2(struct { f01 = 5, f02 = true })

function f1(x: st(st0), y: st(st0)) -> bool = x == y
function f2(x: un(st0), y: un(st0)) -> bool = x == y
function f3(x: stalias1, y: stalias1) -> bool = x == y
function f4(x: unalias1, y: unalias1) -> bool = x == y
function f5(x: stalias2(st0), y: stalias2(st0)) -> bool = x == y
function f6(x: unalias2(st0), y: unalias2(st0)) -> bool = x == y
