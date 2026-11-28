default Order dec

$include <prelude.sail>
$include <vector.sail>
$include <generic_equality.sail>

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

union Seq = {
  Stop : Id(unit),
  Next : Identity(Seq),
}

union Wrap = {
  Wrap : List(Wrap),
}

union A = {
  A1 : B(A),
  A2 : unit,
}

and struct B('a) = {
  f : 'a,
}

newtype N = N : list(N)

union Expr = {
  Lit : bits(32),
  Add : (Expr, Expr),
  Args : vector(2, Expr),
}

struct Holder = {
  name : string,
  tree : Tree,
}

register R : Tree = Leaf(0)

val list_length : forall ('a : Type). List('a) -> int

function list_length(xs) = {
  match xs {
    Nil() => 0,
    Cons(struct { tl, _ }) => 1 + list_length(tl),
  }
}

val list_sum : List(int) -> int

function list_sum(xs) = match xs {
  Nil() => 0,
  Cons(struct { hd, tl }) => hd + list_sum(tl),
}

val list_rev : forall ('a : Type). (List('a), List('a)) -> List('a)

function list_rev(xs, acc) = match xs {
  Nil() => acc,
  Cons(struct { hd, tl }) => list_rev(tl, Cons(struct { hd, tl = acc })),
}

val range : (int, int) -> List(int)

function range(n, m) = if n > m then Nil() else Cons(struct { hd = n, tl = range(n + 1, m) })

val tree_sum : Tree -> int

function tree_sum(t) = match t {
  Leaf(n) => n,
  Node(l, r) => tree_sum(l) + tree_sum(r),
}

val is_cons : list(Rose(int)) -> bool

function is_cons(xs) = match xs { _ :: _ => true, [||] => false }

val rose_sum : Rose(int) -> int

function rose_sum(r) = {
  var total = r.label;
  var cs = r.children;
  while is_cons(cs) do {
    match cs {
      c :: rest => {
        total = total + rose_sum(c);
        cs = rest
      },
      [||] => (),
    }
  };
  total
}

val bar_depth : forall ('a : Type). Bar('a) -> int

function bar_depth(b) = match b {
  Done(_) => 0,
  More(foo) => 1 + bar_depth(foo.next),
}

val quux_count : forall ('a : Type). Quux('a) -> int

function quux_count(Ctor(q)) = match q.rest {
  None() => 1,
  Some(q') => 1 + quux_count(q'),
}

val seq_len : Seq -> int

function seq_len(s) = match s {
  Stop(_) => 0,
  Next(struct { ident }) => 1 + seq_len(ident),
}

val wrap_size : Wrap -> int
val wrap_list_size : List(Wrap) -> int

function wrap_size(Wrap(xs)) = 1 + wrap_list_size(xs)

function wrap_list_size(xs) = match xs {
  Nil() => 0,
  Cons(struct { hd, tl }) => wrap_size(hd) + wrap_list_size(tl),
}

val a_depth : A -> int

function a_depth(a) = match a {
  A1(b) => 1 + a_depth(b.f),
  A2() => 0,
}

val n_size : N -> int
val n_list_size : list(N) -> int

function n_size(N(xs)) = 1 + n_list_size(xs)

function n_list_size(xs) = match xs {
  [||] => 0,
  x :: rest => n_size(x) + n_list_size(rest),
}

val eval : Expr -> bits(32)

function eval(e) = match e {
  Lit(n) => n,
  Add(x, y) => eval(x) + eval(y),
  Args(v) => eval(v[0]) + eval(v[1]),
}

val main : unit -> unit

function main() = {
  let xs : List(int) = range(1, 10);
  print_int("len = ", list_length(xs));
  print_int("sum = ", list_sum(xs));
  let ys = list_rev(xs, Nil());
  print_int("rev len = ", list_length(ys));
  print_endline(if xs == xs then "xs == xs" else "xs != xs");
  print_endline(if xs == ys then "xs == ys" else "xs != ys");
  print_endline(if list_rev(ys, Nil()) == xs then "rev rev == xs" else "rev rev != xs");

  var t : Tree = Node(Leaf(3), Node(Leaf(4), Leaf(5)));
  print_int("tree = ", tree_sum(t));
  t = Node(t, t);
  print_int("tree = ", tree_sum(t));
  let t2 = t;
  t = Leaf(1);
  print_int("t2 = ", tree_sum(t2));
  print_int("t = ", tree_sum(t));

  R = Node(Leaf(10), Leaf(20));
  R = Node(R, R);
  print_int("R = ", tree_sum(R));

  var h : Holder = struct { name = "h", tree = Leaf(1) };
  h.tree = Node(h.tree, h.tree);
  print_int("h = ", tree_sum(h.tree));

  let r : Rose(int) = struct { label = 1, children = [|struct { label = 2, children = [||] }, struct { label = 3, children = [|struct { label = 4, children = [||] }|] }|] };
  print_int("rose = ", rose_sum(r));

  let b : Bar(unit) = More(struct { len = 32, next = More(struct { len = 32, next = Done() }) });
  print_int("bar = ", bar_depth(b));

  let q : Quux(int) = Ctor(struct { f = 1, rest = Some(Ctor(struct { f = 2, rest = None() })) });
  print_int("quux = ", quux_count(q));

  let s : Seq = Next(struct { ident = Next(struct { ident = Stop(struct { ident = () }) }) });
  print_int("seq = ", seq_len(s));

  let w : Wrap = Wrap(Cons(struct { hd = Wrap(Nil()), tl = Cons(struct { hd = Wrap(Nil()), tl = Nil() }) }));
  print_int("wrap = ", wrap_size(w));

  let a : A = A1(struct { f = A1(struct { f = A2() }) });
  print_int("a = ", a_depth(a));

  let n : N = N([|N([||]), N([|N([||])|])|]);
  print_int("n = ", n_size(n));

  let e : Expr = Add(Lit(0x0000_0001), Args([Lit(0x0000_0002), Add(Lit(0x0000_0003), Lit(0x0000_0004))]));
  print_bits("e = ", eval(e));
}
