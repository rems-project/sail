default Order dec
$include <prelude.sail>

scattered enum foo
enum clause foo = Abc
enum clause foo = Def
end foo

struct bar = {
  field1: int,
  field2: foo,
}
