default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

// We have some support for turning comparisons against literals into pattern matches 

union Foo = {
  Bar : int
}

$option --lean-non-beq-type Foo

let mybar = Bar(456)

function test(x : Foo) -> int = if x == Bar(10) then 1 else if Bar(15) == x then 2 else if (x == Bar(123)) : bool then 3 else if mybar == x then 4 else 5
