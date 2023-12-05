default Order dec
$include <prelude.sail>

function example1() -> unit = {
    let l : list(int) = [|1, 2, 3|]
}

function example2() -> unit = {
    let l : list(int) = 1 :: 2 :: 3 :: [||]
}
