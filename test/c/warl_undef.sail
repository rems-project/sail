default Order dec

$option -undefined_gen

$include <prelude.sail>

val "eq_anything" : forall ('a: Type). ('a, 'a) -> bool

overload operator == = {eq_anything}

function neq_anything forall ('a: Type). (x: 'a, y: 'a) -> bool =
  not_bool(x == y)

overload operator != = {neq_anything}

val "print_endline" : string -> unit

struct WARL_range = {
  rangelist : list(int),
}

let x : WARL_range = struct {
  rangelist = [|0, 1|]
}

function main () : unit -> unit = {
  let z: WARL_range = undefined;
  print_endline("ok")
}
