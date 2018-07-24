default Order dec

$include <flow.sail>
$include <exception_basic.sail>

val eq = "eq_anything" : forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq}

val neq : forall ('a : Type). ('a, 'a) -> bool

overload operator != = {neq}

overload ~ = {not_bool}

function neq(x, y) = ~(eq(x, y))

struct S = {
  field1: int,
  field2: vector(8, dec, bit)
}

val "print" : string -> unit

val main : unit -> unit effect {escape}

function main() = {
  let s : S = struct {
    field1 = 4,
    field2 = 0xFF
  };
  assert(s == s, "1");
  assert(~(s == { s with field2 = 0xAB }), "2");
  assert(s != { s with field1 = 5}, "3");
  assert(s == { s with field2 = 0xFF });
  assert({ s with field1 = 0} == {s with field1 = 0});
  print("ok\n")
}