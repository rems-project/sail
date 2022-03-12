default Order dec

$include <prelude.sail>
$include <option.sail>

val test : unit -> int

function test() = {
    let x = Some(0b00);
    match x {
        Some(0b00) => 1,
        Some(0b01) => 2,
        Some(0b10) => 3,
        Some(0b11) => 4,
        None() => 5,
    }
}

let y = test()
