default Order dec

$include <prelude.sail>

union List('a) = {
  Nil  : unit,
  Cons : Cell('a),
}

and struct Cell('a) = {
  hd : 'a,
  tl : List('a),
}

union Tree = {
  Leaf : int,
  Node : (Tree, Tree),
}

struct Rose('a) = {
  label : 'a,
  children : list(Rose('a)),
}

struct Foo('a : Int) = {
  len : int('a),
  next : Bar(unit),
}

and union Bar('a : Type) = {
  Done : 'a,
  More : Foo(32),
}

union Quux('a) = {
  Ctor : { f : 'a, rest : option(Quux('a)) }
}

struct Identity('a) = {
  ident : 'a,
}

type Id('a) = Identity('a)

// A value of a struct type exists only if its fields do
union Seq = {
  Stop : Id(unit),
  Next : Identity(Seq),
}

// A list can be empty, so List(Wrap) does not require a Wrap
union Wrap = {
  Wrap : List(Wrap),
}

// Polymorphic recursion
union Nested('a) = {
  NNil : unit,
  NCons : ('a, Nested(('a, 'a))),
}

union A = {
  A1 : B(A),
  A2 : unit,
}

and struct B('a) = {
  f : 'a,
}

val list_length : forall ('a : Type). List('a) -> int

function list_length(xs) = {
  match xs {
    Nil() => 0,
    Cons(struct { tl, _ }) => 1 + list_length(tl),
  }
}

val tree_sum : Tree -> int

function tree_sum(t) = {
  match t {
    Leaf(n) => n,
    Node(l, r) => tree_sum(l) + tree_sum(r),
  }
}

val test : unit -> unit

function test() = {
  let xs : List(int) = Cons(struct { hd = 1, tl = Cons(struct { hd = 2, tl = Nil() }) });
  let _ : int = list_length(xs);
  let _ : int = tree_sum(Node(Leaf(3), Node(Leaf(4), Leaf(5))));
  let _ : Bar(unit) = More(struct { len = 32, next = Done() });
  let _ : Rose(int) = struct { label = 1, children = [||] };
  ()
}
