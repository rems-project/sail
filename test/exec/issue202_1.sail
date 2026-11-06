default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
    let list_a : list(int) = [| 0 |];
    let list_b : list(int) = 1 :: list_a;
    let list_c : list(int) = 2 :: list_a;
    match list_c {
        c :: a :: [||] => {
            print_int("c = ", c);
            print_int("a = ", a);
        },
        _ => (),
    };
    match list_b {
        [|b, a|] => {
            print_int("b = ", b);
            print_int("a = ", a);
        },
        _ => (),
    };
    match list_a {
        a :: [||] => print_int("a = ", a),
        _ => (),
    };
    print_endline("done")
}
