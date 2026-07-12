// A type with wrong convention
type my_type = int

// A function with wrong convention
function My_Function(x : int) -> int = x

// A variable with wrong convention
function test_variable() -> unit = {
  let My_Var = 1;
  ()
}

// A constant with wrong convention
let my_const = 12

// Variant with wrong constructor case
union My_Union = {
  my_constructor: int
}

// Enum with wrong member case
enum My_Enum = { my_member }

// Scattered enum
scattered enum my_scattered_enum

enum clause my_scattered_enum = My_Member

// Scattered variant
scattered union my_scattered_variant

union clause my_scattered_variant = My_Variant_Constructor : int