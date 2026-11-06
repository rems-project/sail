default Order dec

$include <prelude.sail>

val eq_string = "eq_string" : (string, string) -> bool
val string_startswith = "string_startswith" : (string, string) -> bool
val string_drop = "string_drop" : (string, nat) -> string
val string_length = "string_length" : string -> nat
val string_append = "string_append" : (string, string) -> string

val eq_real = "eq_real" : (real, real) -> bool

val eq_anything = {
    ocaml: "(fun x y -> x = y)",
    interpreter: "eq_anything"
  } : forall ('a : Type). ('a, 'a) -> bool

val length = "length" : forall 'n ('a : Type). vector('n, dec, 'a) -> atom('n)

overload operator == = {eq_string, eq_real, eq_anything}

overload ~ = {not_bool, not_vec}

val print = "print_endline" : string -> unit
