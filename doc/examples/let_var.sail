default Order dec

$include <prelude.sail>

/*!
The above block has type `int` and evaluates to the value `6`.
*/
function example() -> int = {
    {
        let x : int = 3;
        var y : int = 2;
        y = y + 1;
        x + y
    }
}