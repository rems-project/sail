type MyType = int

function my_function(x : int) -> int = x

function test_variable_scoping() -> unit = {
  let my_var = 1;
  ()
}

let MY_CONST = 12

union MyUnion = {
  MyConstructor: int
}

enum MyEnum = { MyMember }

scattered enum MyScatteredEnum

enum clause MyScatteredEnum = MyScatteredMember

scattered union MyScatteredVariant

union clause MyScatteredVariant = MyScatteredVariantConstructor : int