default Order dec
$include <prelude.sail>

// When a struct update does not fit on one line, the fields after a value
// that is broken onto its own line must not start left of the first field,
// where Lean does not read them as part of the structure instance.

struct foo = {
  first_long_field_name : bool,
  second_long_field_name : bool,
  third_long_field_name : bool,
  fourth_long_field_name : bool,
}

function f(s : foo) -> foo =
  { s with first_long_field_name = true, second_long_field_name = false, third_long_field_name = true, fourth_long_field_name = false }

function g(current_state : foo, b : bool) -> foo =
  { current_state with first_long_field_name = if b then true else false, second_long_field_name = b }
