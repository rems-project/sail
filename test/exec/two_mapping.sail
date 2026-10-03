default Order dec

$include <prelude.sail>
$include <string.sail>
$include <generic_equality.sail>

enum R = {X, Y, F, G}

val name : R -> string

function name X = "X"
and name Y = "Y"
and name F = "F"
and name G = "G"

register R1 : bool
register R2 : bool

val p1 : unit -> bool

function p1() = R1

val p2 : unit -> bool

function p2() = R2

val string1 : bits(1) <-> R

mapping string1 = {
  0b0 <-> X,
  0b1 <-> Y
}

val string2 : bits(1) <-> R

mapping string2 = {
  0b0 <-> F,
  0b1 <-> G
}

val test : bits(1) <-> R

mapping test = {
  string1(reg) if p1() <-> reg,
  string2(reg) if p2() <-> reg,
}

val main : unit -> unit

function main() = {
  R1 = true;
  R2 = false;
  print_endline(name(test(0b0)));
  print_endline(name(test(0b1)));
  R1 = false;
  R2 = true;
  print_endline(name(test(0b0)));
  print_endline(name(test(0b1)));
  R1 = true;
  R2 = true;
  print_endline(name(test(0b0)));
  print_endline(name(test(0b1)));
}
