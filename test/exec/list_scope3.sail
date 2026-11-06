default Order dec

$include <prelude.sail>

val test : list(string) -> list(string)

function test(xs) = {
    match xs {
        [|a|] => [|"0", a|],
        _ => [||],
    }
}

val main : unit -> unit

function main() = {
    let ws = test([|"A"|]);
    match ws {
        [|_, a|] => print_endline(a),
        _ => (),
    }    
}
