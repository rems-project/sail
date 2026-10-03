default Order dec
$include <prelude.sail>

val big0 : unit -> int

function big0() = 0

val big1 : unit -> int

function big1() = 1

val big6 : unit -> int

function big6() = 6

val main : unit -> unit

function main() = {
    print_int("0 -> ", 2 ^ 0);
    print_int("0 -> ", 2 ^ big0());
    print_int("1 -> ", 2 ^ 1);
    print_int("1 -> ", 2 ^ big1());
    print_int("6 -> ", 2 ^ 6);
    print_int("6 -> ", 2 ^ big6());
}