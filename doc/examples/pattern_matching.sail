default Order dec
$include <prelude.sail>
$include <string.sail>

val f : unit -> int

val example : unit -> unit

function example() = {
    let n: int = f();
    match n {
        1 => print_endline("1"),
        2 => print_endline("2"),
        3 => print_endline("3"),
        _ => print_endline("wildcard"),
    }
}

function match_switch(expression: int) -> unit = {
    match expression {
        1 => print_endline("expression == 1"),
        2 => {
            // A match arm can have a single expression or a block
            // (because blocks in Sail are also expressions!)
            print_endline("expression == 2")
            // Note that unlike in C, no 'break' is needed as there is no fallthrough
        },
        _ => print_endline("This wildcard pattern acts like default: in a C switch")
    }
}

function match_bind(x: int, y: int) -> unit = {
    match x + y {
        1 => print_endline("x + y == 1"),
        z => {
            // here z is a new variable defined as x + y.
            print_int("x + y = ", z)
            // z is only defined within the match arm
        },
    }
}

function match_destruct(pair: (int, int)) -> unit = {
    match pair : (int, int) {
        (first, second) => {
            // here we have split a pair into two variables first and second
            print_int("first = ", first);
            print_int("second = ", second)
        }
    }
}

struct my_struct = {
    field1 : bits(16),
    field2 : int,
}

function match_struct(value: my_struct) -> unit = {
    match value {
        // match against literals in the struct fields
        struct { field1 = 0x0000, field2 = 3 } => (),

        // bind the struct field values to immutable variables
        struct { field1 = x, field2 = y } => {
            print_bits("value.field1 = ", x);
            print_int("value.field2 = ", y)
        }
    }
}

function match_struct2(value: my_struct) -> unit = {
    match value {
        struct { field1 = x, _ } => {
            print_bits("value.field1 = ", x)
        }
    }
}

/*!
You may wonder -- why not write `z if z < 0` for the final case? Here
we run into one of the limitations of the exhaustiveness checker
mentioned above. Sail can only check the exhaustiveness of _unguarded_
clauses, meaning that the checker only considers cases without an `if`
guard. The `z` pattern by itself is exhaustive, so the checker is
happy, but if we added a `if z < 0` guard the checker would complain
that there are no unguarded patterns for it to look at. This may seem
suprising for such a simple case (we can easily see the three guards
would cover all cases!), however each guard clause could contain
arbitrarily complex logic potentially abstracted behind arbitrary
function calls, which the completeness checker cannot reason about.
*/
function match_guard(x: int, y: int) -> unit = {
    match x + y {
        z if z > 0  => print_endline("y is greater than 0"),
        z if z == 0 => print_endline("z is equal to 0"),
        z           => print_endline("z is less than 0"),
    }
}

enum E = A | B | C

function match_enum(x: E) -> unit = {
    match x {
        A => print_endline("A"),
        B => print_endline("B"),
        C => print_endline("C")
    }
}

function match_tuple() -> unit = {
    let x: (int, int) = (2, 3);
    match x {
        (y, z) => print_endline("y = 2 and z = 3")
    }
}

$span start OPTION
$include <option.sail>

val g : unit -> option(int)

function match_union() -> unit = {
    let x = g();
    match x {
        Some(n) => print_int("n = ", n),
        None()  => print_endline("got None()!"),
    }
}
$span end

function match_cons(ys: list(int)) -> unit = {
    match ys {
        x :: xs => print_endline("cons pattern"),
        [||]    => print_endline("empty list")
    }
}

function match_list(ys: list(int)) -> unit = {
    match ys {
        [|1, 2, 3|] => print_endline("list pattern"),
        _           => print_endline("wildcard")
    }
}

function match_cons_as(ys: list(int)) -> unit = {
    match (1 :: 2 :: ys) : list(int) {
        x :: xs as zs => print_endline("cons with as pattern"),
        [||]          => print_endline("empty list"),
    }
}

/*!
When translating to a target without bitvector literals, this would be
rewritten to use guards:
```sail
match (x, y) {
    (t1, _) if t1 == 0b1 => print_endline("1"),
    (_, t2) if t2 == 0b0 => print_endline("2"),
    (t1, t2) if t1 == 0b0 & t2 == 0b1 => print_endline("3"),
}
```

Most targets that check pattern exhaustiveness share the same limitation
as Sail -- they only check match arms without guards, so they
would not see that this match is complete. To avoid this, Sail will
attempt to replace literal patterns with wildcards when possible, so
the above will be rewritten to:
```sail
match (x, y) {
    (0b1, _) => print_endline("1"),
    (_, 0b0) => print_endline("2"),
    (_, _)   => print_endline("3"),
}
```
which is equivalent.
*/
function match_wildcard_remove(x: bits(1), y: bits(1)) -> unit = {
    match (x, y) {
        (0b1, _)   => print_endline("1"),
        (_, 0b0)   => print_endline("2"),
        (0b0, 0b1) => print_endline("3"),
    }
}
