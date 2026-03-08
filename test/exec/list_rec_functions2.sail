default Order dec

$include <prelude.sail>
$include <string.sail>

val list_hd : forall ('a : Type). list('a) -> option('a)

function list_hd(xs) = match xs {
    [||] => None(),
    x :: xs => Some(x),
}

val list_length : forall ('a : Type). list('a) -> int

function list_length(xs) = match xs {
    [||] => 0,
    _ :: tail => 1 + list_length(tail),
}

val list_append : forall ('a : Type). (list('a), list('a)) -> list('a)

function list_append(xs, ys) = match xs {
    [||] => ys,
    x :: xs => x :: list_append(xs, ys),
}

val list_rev : forall ('a : Type). list('a) -> list('a)

val list_rev2 : forall ('a : Type). list('a) -> list('a)

function list_rev(xs) = match xs {
    [||] => [||],
    x :: xs => list_append(list_rev2(xs), [|x|]),
}

function list_rev2(xs) = match xs {
    [||] => [||],
    x :: xs => list_append(list_rev(xs), [|x|]),
}

val int_list_str : list(int) -> string

function int_list_str(xs) = match xs {
   [||] => "",
   [|x|] => dec_str(x),
   x :: xs => concat_str(dec_str(x), concat_str(", ", int_list_str(xs))),
}

val print_int_list : list(int) -> unit

function print_int_list(xs) =
    print_endline(concat_str("[|", concat_str(int_list_str(xs), "|]")))

val main : unit -> unit

function main() = {
    let xs: list(int) = [|1, 2, 3, 4, 5, 6, 7|];
    print_int_list(xs);
    print_int_list(list_rev(xs));
    print_int("list_length(xs) == ", list_length(xs));
    let ys: list(int) = 8 :: 9 :: [||];
    print_int_list(ys);
    let zs = list_append(xs, ys);
    print_int_list(zs);
    match list_hd(zs) {
        Some(z) => print_int("", z),
        None() => (),
    };
    match list_hd(list_rev(zs)) {
        Some(z) => print_int("", z),
        None() => (),
    };
    print_int("list_length(zs) == ", list_length(zs));
    match zs {
        z1 :: z2 :: ws => {
            print_int_list(ws);
            print_int("", z1);
            print_int("", z2);
            print_int("list_length(ws) == ", list_length(list_rev(list_rev(ws))));
            match list_hd(ws) {
                Some(w) => print_int("", w),
                None() => (),
            }
        },
        _ => (),
    };
    let zs = list_rev(zs);
    print_int("list_length(zs) == ", list_length(zs))
}
