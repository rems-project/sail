default Order dec

$include <prelude.sail>

struct rectangle = {
    width : int,
    height : int,
}

$span start SHAPE
struct circle = { radius : int }

union shape = {
    Rectangle : rectangle,
    Circle : circle,
}
$span end

val example : unit -> unit

function example() = {
    // Construct a shape using the Rectangle constructor
    let r : shape = Rectangle(struct { width = 30, height = 20 });

    // Construct a shape using the Circle constructor
    // Note that we can allow the 'shape' type to be inferred
    let c = Circle(struct { radius = 15 });
}

$span start EX_UNIT
union example_unit_constructor = {
  Foo : (int, string),
  Bar : unit,
}

// Using a constructor with a tuple type
let x1 = Foo(2, "a string")

// Note that the above is equivalent to
let x2 = Foo((2, "a string"))

// Using a unit-type constructor
let y1 = Bar()

// Similarly, equivalent to
let y2 = Bar(())
$span end

union shape2 = {
    Rectangle2 : { width : int, height : int },
    Circle2 : { radius : int },
}

union either('a, 'b) = {
    Left : 'a,
    Right : 'b,
}
