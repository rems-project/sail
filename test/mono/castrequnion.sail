default Order dec
$include <prelude.sail>
$include <mono_rewrites.sail>

val foo : forall 'm 'n, 'm in {8,16} & 'n in {16,32,64}. (implicit('n), bits('m)) -> option(bits('n)) effect pure

function foo(n, x) =
  let y : bits(16) = sail_zero_extend(x,16) in
  match 'n {
    16 => None(),
    32 => Some(y@y),
    64 => let z = y@y@y@y in let dfsf = 4 in Some(z)
  }

union Result ('a : Type) = {
  Value : ('a, int),
  Complaint : string
}

val bar : forall 'n, 'n in {8,16,32}. bits('n) -> Result(bits(2*'n))

function bar(x) =
  match 'n {
    8 => Complaint("No bytes"),
   16 => Value(x@x, unsigned(x)),
   32 => Value(sail_sign_extend(x,64), unsigned(x))
  }

val baz : forall 'n, 'n in {8,16,32}. bits('n) -> Result(bits(2*'n))

function baz(x) = {
  if 'n == 16 then Value(x@x, unsigned(x))
  else if 'n == 32 then Value(sail_sign_extend(x,64), unsigned(x))
  else Complaint("No bytes")
}

val cmp : forall 'n. (option(bits('n)), option(bits('n))) -> bool

function cmp (None(),None()) = true
and cmp (None(),Some(_)) = false
and cmp (Some(_),None()) = false
and cmp (Some(x),Some(y)) = x == y

overload operator == = {cmp}

val run : unit -> unit

function run() = {
  assert((foo(0x12) : option(bits(16))) == None());
  assert((foo(0x12) : option(bits(32))) == Some(0x00120012));
  assert((foo(0x12) : option(bits(64))) == Some(0x0012001200120012));
}
