default Order dec

$include <prelude.sail>

val test : forall ('a : Type). list('a) -> list('a)

function test(xs) = {
    let ys = {
        let zs = xs;
        zs
    };
    ys
}

val main : unit -> unit

function main() = {
    let ws: list(string) = [|"A", "B", "C"|];
    let ws = {
        let ws = test(ws);
        ws
    };
    match ws {
        [|a, b, c|] => {
            print_endline(a);
            print_endline(b);
            print_endline(c)
        },
        _ => print_endline("no match"),
    }
}
